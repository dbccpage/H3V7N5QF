from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, changes, perform
from ninth.cost import GIVEN_SIZE, cost, cost_eighth, cost_part, part_costs, raises_by_one
from ninth.explore import explore
from ninth.reach import mutual, reach_graph, reachable, reachable_by_search, reachable_eighth, reachable_in_graph, reachable_on_part
from ninth.state import DState, canonical, empty, swap


def test_the_cost_is_the_size_and_only_additions_raise_it() -> None:
    assert GIVEN_SIZE == 0 and cost(empty()) == 0 and cost(DState.of(1, [], [])) == 1
    assert cost(DState.of(2, [(0, 1), (0, 1)], [(1, 1)])) == 5
    with pytest.raises(ValueError):
        cost(DState.of(1, [], [], (0, 0)))
    s = DState.of(2, [(0, 1)], [])
    for change in changes(s):
        assert raises_by_one(s, change) == (cost(perform(s, change)) == cost(s) + 1)
    assert raises_by_one(empty(), Change(Kind.ADD_TERM))
    one = DState.of(1, [], [])
    cost_r, cost_s = part_costs(one)
    assert cost_r == cost_part(one.r_part()) == 1 and cost_s == 1
    assert cost_r + one.total_s == cost(one) == cost_s + one.total_r
    assert sum(part_costs(one)) == cost(one) + one.n


def test_the_eighth_seeds_cost_is_cited_and_differs() -> None:
    one = DState.of(1, [], [])
    assert cost_eighth(one, False) == 2 and cost_eighth(one, True) == 3 and cost(one) == 1
    ara, asa = DState.of(1, [(0, 0)], []), DState.of(1, [], [(0, 0)])
    assert cost(ara) == cost(asa) == 2 and cost_eighth(ara, False) == 1 and cost_eighth(asa, False) == 3
    arb = DState.of(2, [(0, 1)], [])
    assert cost_eighth(arb, False) == 0 and cost(arb) == 3
    with pytest.raises(ValueError):
        cost_eighth(empty(), False)
    for state in explore(empty(), 3, 5).depth:
        if state.n >= 1:
            assert cost_eighth(state, False) != cost(state)
            cr, cs = part_costs(state)
            assert cr + state.total_s == cost(state) == cs + state.total_r
            assert cr + cs == cost(state) + state.n


def test_the_criterion_a_term_decides() -> None:
    start, one, two = empty(), DState.of(1, [], []), DState.of(2, [(0, 0)], [(1, 0)])
    assert reachable(start, start) and reachable(start, one) and reachable(start, two)
    assert reachable(one, two) and reachable(two, one) and mutual(one, two)
    assert not reachable(one, start) and not reachable(two, start) and not mutual(start, one)
    assert reachable_on_part(start, one, "r") and reachable_on_part(start, one, "s")
    assert reachable_eighth(one, two) and reachable_eighth(two, one)
    assert reachable_on_part(one, two, "r") == reachable(one, two)
    with pytest.raises(ValueError):
        reachable(DState.of(1, [], [], (0, 0)), one)


def test_the_criterion_agrees_with_a_search() -> None:
    bound, rounds = 3, 5
    expl = explore(start := empty(), bound, rounds)
    wide = explore(start, bound, rounds + 2)
    graph = reach_graph(wide)
    states = sorted(expl.depth, key=lambda s: s.key())
    for s in states:
        found = reachable_in_graph(graph, s) & set(states)
        assert {t for t in states if reachable(s, t)} == found
    one = DState.of(1, [], [])
    assert reachable_by_search(one, 2, 6) >= {canonical(DState.of(2, [(0, 1)], [])), one, canonical(swap(DState.of(1, [(0, 0)], [])))}
    assert empty() not in reachable_by_search(one, 2, 6)
    assert empty() in reachable_by_search(empty(), 2, 2)
