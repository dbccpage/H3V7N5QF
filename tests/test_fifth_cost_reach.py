from __future__ import annotations

from itertools import product

import pytest

from fifth.changes import Change, Kind, changes, obstruction, perform
from fifth.cost import (
    contains_given,
    cost,
    cost_anchored,
    cost_free,
    cost_free_by_placement,
    given_size,
    has_two_way,
    lost,
    lost_free,
    raises_by_one,
)
from fifth.explore import explore, performed
from fifth.reach import (
    contains,
    embedding,
    mutual,
    reach_graph,
    reachable,
    reachable_by_search,
    reachable_fourth,
    reachable_in_graph,
)
from fifth.state import MState, canonical, given
from xry.state import Sameness

ARB = given(False, Sameness.ANCHORED)
BOTH = given(True, Sameness.ANCHORED)
EMPTY = MState.of(2, [], (0, 1))
ONE = MState.of(1, [], (0, 0))
MERGED = MState.of(2, [(0, 1)], (0, 0))


def test_destroyed_givens() -> None:
    with pytest.raises(ValueError):
        lost(given(False, Sameness.FREE), False)
    assert lost(ARB, False) == 0 and lost(ARB, True) == 1
    assert lost(BOTH, True) == 0 and lost(EMPTY, False) == 1 and lost(EMPTY, True) == 2
    assert lost(ONE, False) == 2 and lost(ONE, True) == 3 and lost(MERGED, True) == 3
    assert lost(MState.of(2, [(1, 0)], (0, 1)), True) == 1
    assert lost_free(MState.of(1, []), False) == 2 and lost_free(MState.of(3, []), True) == 2
    assert lost_free(MState.of(2, [(0, 1)]), True) == 1 and lost_free(MState.of(2, [(0, 1), (1, 0)]), True) == 0
    assert lost_free(MState.of(2, [(0, 1), (0, 1)]), False) == 0


def test_cost_in_closed_form() -> None:
    assert given_size(False) == 3 and given_size(True) == 4
    assert contains_given(ARB, False) and has_two_way(BOTH)
    assert cost_anchored(ARB, False) == 0 and cost_anchored(BOTH, True) == 0
    assert cost_anchored(BOTH, False) == 1 and cost_anchored(ARB, True) == 1  # remove bra
    assert cost_anchored(EMPTY, False) == 1 and cost_anchored(EMPTY, True) == 2
    assert cost_anchored(ONE, False) == 2 and cost_anchored(ONE, True) == 3
    assert cost_anchored(MERGED, False) == 4  # remove arb, identify, add the term, add arc
    assert cost_anchored(MState.of(2, [(0, 1), (1, 1)], (0, 1)), False) is None
    assert cost_anchored(MState(0, (), None), False) is None
    assert cost_free(MState.of(1, []), False) == 2 and cost_free(MState.of(2, []), False) == 1
    assert cost_free(MState.of(2, [(0, 1)]), True) == 1 and cost_free(MState.of(3, [(1, 2), (2, 1)]), True) == 1
    assert cost_free(MState.of(2, [(0, 1), (0, 1), (0, 1)]), False) == 2
    assert cost_free(MState.of(2, [(0, 0)]), False) is None and cost_free_by_placement(MState.of(2, [(0, 0)]), False) is None
    assert cost(ONE, False) == 2 and cost(MState(2, EMPTY.mult), False) == 1
    for bra in (False, True):
        for n in (1, 2, 3):
            for mult in product(range(3), repeat=n * n):
                state = MState(n, mult)
                assert cost_free(state, bra) == cost_free_by_placement(state, bra)


def test_which_changes_raise_the_cost_by_one() -> None:
    with pytest.raises(ValueError):
        raises_by_one(given(False, Sameness.FREE), Change(Kind.ADD_TERM), False)
    assert raises_by_one(ARB, Change(Kind.ADD_TERM), False)
    assert raises_by_one(ARB, Change(Kind.ADD_ASSERTION, 0, 1), False)  # arb twice
    assert raises_by_one(ARB, Change(Kind.ADD_ASSERTION, 1, 0), False)  # bra, not given
    assert not raises_by_one(ARB, Change(Kind.ADD_ASSERTION, 1, 0), True)  # restores bra
    assert raises_by_one(ARB, Change(Kind.REMOVE, 0, 1), False)  # destroys arb
    assert not raises_by_one(MState.of(2, [(0, 1), (0, 1)], (0, 1)), Change(Kind.REMOVE, 0, 1), False)
    assert raises_by_one(EMPTY, Change(Kind.IDENTIFY, 0, 1), False)
    assert not raises_by_one(MState.of(3, [], (0, 1)), Change(Kind.IDENTIFY, 0, 2), False)
    assert not raises_by_one(MState.of(2, [], (0, 0)), Change(Kind.IDENTIFY, 0, 1), False)
    assert not raises_by_one(MERGED, Change(Kind.REMOVE, 0, 1), False)
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 3, 6)
        for state, change, out in performed(expl):
            assert raises_by_one(state, change, bra) == (cost(out, bra) == expl.depth[state] + 1)


def test_reachability_is_decided_by_the_names() -> None:
    with pytest.raises(ValueError):
        reachable(given(False, Sameness.FREE), ARB)
    assert reachable(ARB, BOTH) and reachable(BOTH, ARB) and mutual(ARB, BOTH)
    assert reachable(ARB, EMPTY) and reachable(EMPTY, ARB) and reachable(ARB, ONE) and reachable(ARB, MERGED)
    assert not reachable(ONE, ARB) and not reachable(MERGED, EMPTY) and reachable(ONE, MERGED) and reachable(MERGED, ONE)
    assert not mutual(ARB, ONE)
    assert not reachable(ARB, MState.of(2, [(0, 0)], (0, 1)))  # illegal target
    assert not reachable(MState.of(2, [(0, 0)], (0, 1)), ARB)
    free = given(False, Sameness.FREE)
    assert reachable(free, MState.of(1, [])) and reachable(MState.of(1, []), free)
    assert not reachable(free, MState(0, ()))
    assert contains(ARB, BOTH) and embedding(ARB, BOTH) == (0, 1) and reachable_fourth(ARB, BOTH)


def test_search_within_a_bound() -> None:
    assert reachable_by_search(ARB, 2, 0) == {canonical(ARB)}
    one = reachable_by_search(ARB, 2, 1)
    assert canonical(EMPTY) in one and canonical(BOTH) in one and len(one) == 4
    assert canonical(ONE) in reachable_by_search(ARB, 2, 2)
    assert canonical(ARB) in reachable_by_search(ONE, 3, 5) or not reachable(ONE, ARB)


@pytest.mark.parametrize(("sameness", "bra"), [(Sameness.FREE, False), (Sameness.ANCHORED, True), (Sameness.ANCHORED, False)])
def test_criterion_agrees_with_the_graph_search(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 4
    expl = explore(given(bra, sameness), bound, rounds)
    graph = reach_graph(explore(given(bra, sameness), bound, rounds + 3))
    results = set(expl.depth)
    assert results <= set(graph)
    for s in results:
        found = reachable_in_graph(graph, s) & results
        assert found == {t for t in results if reachable(s, t)}
        assert s in found
    if sameness is Sameness.FREE:
        assert all(reachable(s, t) for s in results for t in results)
    else:
        merged = [s for s in results if s.names is not None and s.names[0] == s.names[1]]
        apart = [s for s in results if s not in merged]
        assert merged and apart
        assert all(not reachable(s, t) for s in merged for t in apart)
        assert all(reachable(s, t) for s in apart for t in results)
        assert all(reachable(s, t) for s in merged for t in merged)


def test_the_graph_only_holds_performed_changes_among_results() -> None:
    expl = explore(ARB, 2, 3)
    graph = reach_graph(expl)
    for state, outs in graph.items():
        for out in outs:
            assert out in expl.depth
            assert any(
                not obstruction(state, c) and canonical(perform(state, c)) == out for c in changes(state)
            )
        assert len(set(outs)) == len(outs)
    assert graph[canonical(ARB)]
