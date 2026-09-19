from __future__ import annotations

from itertools import product

import pytest

from sixth.changes import Change, Kind, changes, perform
from sixth.cost import (
    contains_given,
    cost,
    cost_anchored,
    cost_free,
    cost_free_by_placement,
    given_size,
    has_off_diagonal,
    has_two_way,
    lost,
    lost_apart_free,
    lost_fifth,
    lost_free,
    lost_merged_free,
    merged_optimal,
    raises_by_one,
)
from sixth.explore import explore, performed
from sixth.reach import mutual, reach_graph, reachable, reachable_by_search, reachable_fifth, reachable_in_graph
from sixth.state import MState, canonical, given
from xry.state import Sameness

ARB = given(False, Sameness.ANCHORED)
BOTH = given(True, Sameness.ANCHORED)
EMPTY = MState.of(2, [], (0, 1))
ONE = MState.of(1, [], (0, 0))
ARA = MState.of(1, [(0, 0)], (0, 0))
ARA2 = MState.of(1, [(0, 0), (0, 0)], (0, 0))
MERGED = MState.of(2, [(0, 1)], (0, 0))


def test_destroyed_givens_with_the_names_one_term_depend_on_crc() -> None:
    with pytest.raises(ValueError):
        lost(given(False, Sameness.FREE), False)
    assert lost(ARB, False) == 0 and lost(ARB, True) == 1
    assert lost(BOTH, True) == 0 and lost(EMPTY, False) == 1 and lost(EMPTY, True) == 2
    assert lost(ONE, False) == 2 and lost(ONE, True) == 3
    assert lost(ARA, False) == 1 and lost(ARA, True) == 2
    assert lost(ARA2, False) == 1 and lost(ARA2, True) == 1
    assert lost(MERGED, False) == 2 and lost(MState.of(2, [(0, 1), (1, 1)], (0, 0)), False) == 2
    # The fifth's formula agrees exactly where crc is not asserted at the named term.
    for state in (ARB, BOTH, EMPTY, ONE, MERGED, MState.of(2, [(0, 1), (1, 1)], (0, 1))):
        assert lost(state, True) == lost_fifth(state, True)
    assert lost_fifth(ARA, False) == 2 != lost(ARA, False)


def test_free_closed_form() -> None:
    assert not has_two_way(MState.of(2, [(1, 1)])) and has_two_way(MState.of(2, [(0, 1), (1, 0)]))
    assert has_off_diagonal(MState.of(2, [(0, 1)])) and not has_off_diagonal(MState.of(2, [(1, 1)]))
    assert lost_apart_free(MState.of(1, [(0, 0)]), False) is None
    assert lost_merged_free(MState.of(1, [(0, 0)]), False) == 1
    with pytest.raises(ValueError):
        lost_merged_free(MState(0, ()), False)
    assert lost_free(MState.of(1, [(0, 0)]), False) == 1 and lost_free(MState.of(1, [(0, 0)]), True) == 2
    assert lost_free(MState.of(2, [(0, 0), (0, 0)]), True) == 1 and lost_free(MState.of(2, []), True) == 2
    assert lost_free(MState.of(2, [(0, 1)]), False) == 0 and lost_free(MState.of(2, [(0, 1)]), True) == 1
    assert lost_free(MState.of(2, [(0, 1), (1, 0)]), True) == 0 and lost_free(MState.of(2, [(1, 1)]), False) == 1
    assert merged_optimal(MState.of(2, [(1, 1)]), False) and merged_optimal(MState.of(1, []), True)
    assert not merged_optimal(MState.of(2, [(0, 1)]), False)
    for bra in (False, True):
        for n in (1, 2, 3):
            for mult in product(range(3), repeat=n * n):
                state = MState(n, mult)
                assert cost_free(state, bra) == cost_free_by_placement(state, bra), (state, bra)


def test_cost_in_closed_form() -> None:
    assert given_size(False) == 3 and given_size(True) == 4
    assert contains_given(ARB, False)
    assert cost_anchored(ARB, False) == 0 and cost_anchored(BOTH, True) == 0
    assert cost_anchored(ARA, False) == 1 and cost_anchored(ARA2, True) == 1  # identify a and b
    assert cost_anchored(ONE, False) == 2 and cost_anchored(ONE, True) == 3
    assert cost_anchored(MState.of(2, [(0, 1), (0, 0)], (0, 1)), False) == 1  # add ara
    assert cost_anchored(MERGED, False) == 4 and cost_anchored(MState.of(2, [(0, 0)], (0, 0)), False) == 2
    assert cost_anchored(MState(0, (), None), False) is None and cost_free(MState(0, ()), True) is None
    assert cost_free_by_placement(MState(0, ()), False) is None
    assert cost_free(MState.of(2, [(0, 0), (0, 0)]), True) == 2  # identify, add a term
    assert cost(ARA, False) == 1 and cost(MState(2, EMPTY.mult), False) == 1


def test_which_changes_raise_the_cost_by_one() -> None:
    with pytest.raises(ValueError):
        raises_by_one(given(False, Sameness.FREE), Change(Kind.ADD_TERM), False)
    assert raises_by_one(ARB, Change(Kind.ADD_TERM), False)
    assert raises_by_one(ARB, Change(Kind.ADD_ASSERTION, 0, 0), False)  # ara
    assert not raises_by_one(ARB, Change(Kind.ADD_ASSERTION, 1, 0), True)  # restores bra
    assert raises_by_one(ARB, Change(Kind.REMOVE, 0, 1), False)
    assert raises_by_one(ARB, Change(Kind.IDENTIFY, 0, 1), False)  # S = 1 = p
    assert not raises_by_one(EMPTY, Change(Kind.IDENTIFY, 0, 1), True) or lost(EMPTY, True) == 2
    assert raises_by_one(EMPTY, Change(Kind.IDENTIFY, 0, 1), False)  # S = 0 = p
    assert not raises_by_one(MState.of(2, [(0, 0)], (0, 1)), Change(Kind.IDENTIFY, 0, 1), False)  # S = 1 > p = 0
    assert raises_by_one(ARA, Change(Kind.REMOVE, 0, 0), False) and not raises_by_one(ARA2, Change(Kind.REMOVE, 0, 0), False)
    assert not raises_by_one(ONE, Change(Kind.ADD_ASSERTION, 0, 0), False) and raises_by_one(ARA, Change(Kind.ADD_ASSERTION, 0, 0), False)
    assert not raises_by_one(MState.of(2, [(1, 1)], (0, 0)), Change(Kind.REMOVE, 1, 1), False)
    assert not raises_by_one(MState.of(3, [], (0, 1)), Change(Kind.IDENTIFY, 0, 2), False)
    assert not raises_by_one(MState.of(2, [], (0, 0)), Change(Kind.IDENTIFY, 0, 1), False)
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 3, 5)
        for state, change, out in performed(expl):
            assert raises_by_one(state, change, bra) == (cost(out, bra) == expl.depth[state] + 1), (state, change)


def test_reachability_is_decided_by_the_names() -> None:
    with pytest.raises(ValueError):
        reachable(given(False, Sameness.FREE), ARB)
    assert reachable(ARB, BOTH) and reachable(BOTH, ARB) and mutual(ARB, BOTH)
    assert reachable(ARB, ARA) and not reachable(ARA, ARB) and reachable(ARA, ONE) and reachable(ONE, ARA2)
    assert reachable(ARB, MState.of(2, [(0, 0), (1, 1)], (0, 1))) and reachable(MState.of(2, [(0, 0)], (0, 1)), ARB)
    assert not mutual(ARB, ARA)
    assert not reachable(MState(0, ()), given(False, Sameness.FREE))
    free = given(False, Sameness.FREE)
    assert reachable(free, MState.of(1, [(0, 0)])) and reachable(MState.of(1, [(0, 0)]), free)
    assert not reachable(free, MState(0, ()))
    assert reachable_fifth(ARB, BOTH) and not reachable_fifth(ONE, ARB)


def test_search_within_a_bound() -> None:
    assert reachable_by_search(ARB, 2, 0) == {canonical(ARB)}
    one = reachable_by_search(ARB, 2, 1)
    assert canonical(EMPTY) in one and canonical(ARA) in one and len(one) == 7
    assert canonical(ONE) in reachable_by_search(ARB, 2, 2)


@pytest.mark.parametrize(("sameness", "bra"), [(Sameness.FREE, False), (Sameness.ANCHORED, True), (Sameness.ANCHORED, False)])
def test_criterion_agrees_with_the_graph_search(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 3
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
        assert merged and apart and any(not s.legal for s in merged)
        assert all(not reachable(s, t) for s in merged for t in apart)
        assert all(reachable(s, t) for s in apart for t in results)
        assert all(reachable(s, t) for s in merged for t in merged)
    legal = [s for s in results if s.legal]
    assert all(reachable(s, t) == reachable_fifth(s, t) for s in legal for t in legal)


def test_the_graph_only_holds_changes_among_results() -> None:
    expl = explore(ARB, 2, 3)
    graph = reach_graph(expl)
    for state, outs in graph.items():
        for out in outs:
            assert out in expl.depth
            assert any(canonical(perform(state, c)) == out for c in changes(state))
        assert len(set(outs)) == len(outs)
    assert graph[canonical(ARB)]
