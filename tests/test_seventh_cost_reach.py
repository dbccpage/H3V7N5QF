from __future__ import annotations

import pytest

from seventh.changes import Change, Kind, changes, perform
from seventh.cost import GIVEN_SIZE, cost, cost_sixth, cost_sixth_free, raises_by_one
from seventh.explore import explore
from seventh.reach import mutual, reach_graph, reachable, reachable_by_search, reachable_in_graph, reachable_sixth
from seventh.state import MState, canonical, empty


def test_the_cost_is_the_size_and_only_additions_raise_it() -> None:
    assert GIVEN_SIZE == 0 and cost(empty()) == 0 and cost(MState.of(1, [])) == 1
    assert cost(MState.of(2, [(0, 1), (0, 1), (1, 1)])) == 5
    with pytest.raises(ValueError):
        cost(MState.of(1, [], (0, 0)))
    s = MState.of(2, [(0, 1)])
    for change in changes(s):
        assert raises_by_one(s, change) == (cost(perform(s, change)) == cost(s) + 1)
    assert raises_by_one(empty(), Change(Kind.ADD_TERM))


def test_the_sixth_seeds_cost_is_cited_and_differs() -> None:
    one = MState.of(1, [])
    assert cost_sixth(one, False) == 2 and cost_sixth(one, True) == 3 and cost(one) == 1
    arb = MState.of(2, [(0, 1)])
    assert cost_sixth(arb, False) == 0 and cost(arb) == 3
    assert cost_sixth_free(empty(), False) is None
    with pytest.raises(ValueError):
        cost_sixth(empty(), False)
    # Without `bra` the sixth's cost has the other parity: never the seventh's.
    for state in explore(empty(), 3, 6).depth:
        if state.n >= 1:
            assert cost_sixth(state, False) != cost(state)


def test_the_criterion_a_term_decides() -> None:
    start, one, two = empty(), MState.of(1, []), MState.of(2, [(0, 0), (1, 0)])
    assert reachable(start, start) and reachable(start, one) and reachable(start, two)
    assert reachable(one, two) and reachable(two, one) and mutual(one, two)
    assert not reachable(one, start) and not reachable(two, start) and not mutual(start, one)
    assert reachable_sixth(one, two) and reachable_sixth(two, one)
    with pytest.raises(ValueError):
        reachable(MState.of(1, [], (0, 0)), one)


def test_the_criterion_agrees_with_a_search() -> None:
    bound, rounds = 3, 5
    expl = explore(start := empty(), bound, rounds)
    wide = explore(start, bound, rounds + 2)
    graph = reach_graph(wide)
    states = sorted(expl.depth, key=lambda s: s.key())
    for s in states:
        found = reachable_in_graph(graph, s) & set(states)
        assert {t for t in states if reachable(s, t)} == found
    assert reachable_by_search(one := MState.of(1, []), 2, 6) >= {canonical(MState.of(2, [(0, 1)])), one}
    assert empty() not in reachable_by_search(one, 2, 6)
    assert empty() in reachable_by_search(empty(), 2, 2)
