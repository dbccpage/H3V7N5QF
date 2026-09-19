from __future__ import annotations

from itertools import product

import pytest

from eighth.changes import Change, Kind, changes, perform
from eighth.cost import cost, cost_free_by_placement, destroyed, given_size, raises_by_one
from eighth.explore import explore
from eighth.reach import mutual, reach_graph, reachable, reachable_by_search, reachable_in_graph, reachable_part
from eighth.state import DState, canonical, given
from sixth.cost import cost as cost_part
from xry.state import Sameness


def test_the_cost_is_the_sixths_on_r_plus_the_s_total() -> None:
    g = given(False, Sameness.ANCHORED)
    assert cost(g, False) == 0 and given_size(False) == 3 and destroyed(g, False) == 0
    with_s = DState.of(2, [(0, 1)], [(0, 1), (1, 1), (0, 0)], (0, 1))
    assert cost(with_s, False) == 3 == (cost_part(with_s.r_part(), False) or 0) + 3
    merged = DState.of(1, [(0, 0)], [(0, 0)], (0, 0))
    assert cost(merged, False) == 2 and cost(merged, True) == 3 and destroyed(merged, False) == 1
    assert cost(DState(0, (), ()), False) is None and cost_free_by_placement(DState(0, (), ()), False) is None
    free = DState.of(2, [(0, 1)], [(1, 0)])
    assert cost(free, False) == 1 == cost_free_by_placement(free, False) and destroyed(free, False) == 0


def test_the_free_closed_form_equals_the_best_placement() -> None:
    for n in (1, 2):
        for r in product(range(2), repeat=n * n):
            for s in product(range(2), repeat=n * n):
                state = DState(n, r, s)
                for bra in (False, True):
                    assert cost(state, bra) == cost_free_by_placement(state, bra)


def test_which_changes_raise_the_cost_by_one() -> None:
    for bra in (False, True):
        for state in explore(given(bra, Sameness.ANCHORED), 3, 3).depth:
            for change in changes(state):
                out = perform(state, change)
                assert raises_by_one(state, change, bra) == (cost(out, bra) == (cost(state, bra) or 0) + 1)
    g = given(False, Sameness.ANCHORED)
    assert raises_by_one(g, Change(Kind.ADD_ASSERTION, "s", 0, 0), False)
    assert not raises_by_one(DState.of(2, [(0, 1)], [(0, 1)], (0, 1)), Change(Kind.REMOVE, "s", 0, 1), False)
    assert not raises_by_one(g, Change(Kind.REMOVE, "r", 0, 1), False) is False  # a given asserted once: raises


def test_the_criterion_is_the_names_on_the_r_part() -> None:
    g = given(False, Sameness.ANCHORED)
    with_s = DState.of(2, [(0, 1)], [(1, 1)], (0, 1))
    merged = DState.of(1, [], [(0, 0)], (0, 0))
    assert reachable(g, with_s) and reachable(with_s, g) and mutual(g, with_s)
    assert reachable(g, merged) and not reachable(merged, g) and not mutual(g, merged)
    assert reachable(merged, DState.of(1, [(0, 0)], [], (0, 0)))
    assert reachable_part(g.r_part(), with_s.r_part())
    free = given(False, Sameness.FREE)
    assert reachable(free, DState.of(1, [], [(0, 0)])) and reachable(DState.of(1, [], [(0, 0)]), free)


@pytest.mark.parametrize(("sameness", "bra"), [(s, b) for s in Sameness for b in (False, True)])
def test_the_criterion_agrees_with_a_search(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 2, 3
    expl = explore(given(bra, sameness), bound, rounds)
    wide = explore(given(bra, sameness), bound, rounds + 3)
    graph = reach_graph(wide)
    states = sorted(expl.depth, key=lambda s: s.key())
    for s in states:
        found = reachable_in_graph(graph, s) & set(states)
        assert {t for t in states if reachable(s, t)} == found
    start = canonical(given(bra, sameness))
    assert start in reachable_by_search(start, 2, 2)
    if not bra:
        assert canonical(DState.of(2, [(0, 1)], [(0, 1)], start.names)) in reachable_by_search(start, 2, 1)
