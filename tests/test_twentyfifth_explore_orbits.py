"""The exploration of states with filled triples, the results formed afterwards, and the independent count."""

from __future__ import annotations

import pytest

from twentythird.state import DState

from twentyfifth.cost import cost
from twentyfifth.explore import explore, explore_states, group, performed, shortest_sequences
from twentyfifth.orbits import classes, counts_within, fill_orbits, stabilizer
from twentyfifth.state import FState, Filling, empty25, result_mark


def test_exploration_refuses_bad_bounds() -> None:
    with pytest.raises(ValueError, match="at least one term"):
        explore_states(0, 3)
    with pytest.raises(ValueError, match="not negative"):
        explore_states(2, -1)


def test_small_exploration_and_grouping() -> None:
    g = explore(3, 5, keep_log=True)
    assert g.bound == 3 and g.rounds == 5
    assert all(cost(g.representative(m)) == r for m, r in g.round_of.items())
    one = result_mark(FState(DState(3, (0,) * 9, (0,) * 9), ((0, 1, 2),)))
    assert g.round_of[one] == 4
    assert g.ordered_marks()[0] == result_mark(empty25())
    assert all(g.fewest_members(m) for m in g.round_of)
    log = g.states.log
    assert any(a.beyond for a in log) and any(isinstance(a.change, Filling) for a in log)
    assert all((a.outcome is None) == a.beyond for a in log)
    assert g.states.frontier and all(fs.n == 3 for fs, _ in g.states.frontier)
    assert len(performed(g.states)) > 0
    seqs = shortest_sequences(g)
    assert seqs[result_mark(empty25())] == 1 and seqs[one] > 0
    assert group(g.states).round_of == g.round_of


def test_two_terms_are_the_twentythird_figures() -> None:
    g = explore(2, 8)
    per_round = [sum(1 for r in g.round_of.values() if r == k) for k in range(9)]
    assert per_round == [1, 1, 3, 6, 13, 24, 39, 58, 81]
    assert not any(m[2] for m in g.round_of)


def test_the_independent_count() -> None:
    g = explore(4, 6)
    explored: dict[str, int] = {}
    for (n, _, filled), r in g.round_of.items():
        label = f"{n}/{r - n - len(filled)}/{len(filled)}"
        explored[label] = explored.get(label, 0) + 1
    assert explored == counts_within(4, 6)
    assert classes(0, 2) == (((0, ()), 0, ()),)
    assert len(stabilizer(3, (0,) * 9)) == 6
    assert fill_orbits(3, stabilizer(3, (0,) * 9), 2) == [1, 1, 1]
    rotations: list[tuple[int, ...]] = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    assert fill_orbits(3, rotations, 2) == [1, 2, 1]
    with pytest.raises(ArithmeticError, match="whole number"):
        fill_orbits(3, [(0, 1, 2), (0, 2, 1), (1, 0, 2)], 1)
