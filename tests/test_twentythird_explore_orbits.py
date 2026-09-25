"""The exploration of states grouped into results, and the independent counts (twenty-third seed)."""

from __future__ import annotations

import pytest

from ninth.explore import explore as explore_ninth
from twentythird.cost import cost
from twentythird.explore import explore, group_depths, shortest_sequences
from twentythird.orbits import (
    counts_within,
    layer_counts,
    listing_counts,
    off_diagonal_tables,
    one_term_count,
    tables,
    three_term_counts,
    two_term_count,
    two_term_count_by_points,
    two_term_round_count,
)
from twentythird.state import empty, nothing_key


def test_grouped_exploration() -> None:
    g = explore(3, 5)
    assert g.bound == 3 and g.rounds == 5
    assert all(cost(g.representative(k)) == r for k, r in g.round_of.items())
    keys = g.ordered_keys()
    assert keys[0] == nothing_key(0) and g.round_of[keys[-1]] == 5
    assert all(g.fewest_members(k) for k in keys)
    seq = shortest_sequences(g)
    assert seq[nothing_key(0)] == 1 and all(v >= 1 for v in seq.values())
    ninth = explore_ninth(empty(), 3, 5)
    assert group_depths(ninth.depth) == g.round_of


def test_counts_agree() -> None:
    for t in range(9):
        assert two_term_count(t) == two_term_count_by_points(t)
    assert listing_counts(2, 5) == [two_term_count(t) for t in range(6)]
    assert listing_counts(3, 4) == three_term_counts(4)
    assert [two_term_round_count(r) for r in range(9)] == [1, 1, 3, 6, 13, 24, 39, 58, 81]
    assert [one_term_count(t) for t in range(3)] == [1, 2, 2]
    assert layer_counts(5) == [1, 1, 3, 7, 18, 58]
    g = explore(4, 6)
    got: dict[str, int] = {}
    for k, r in g.round_of.items():
        got[f"{k[0]}/{r - k[0]}"] = got.get(f"{k[0]}/{r - k[0]}", 0) + 1
    assert got == counts_within(4, 6)


def test_tables() -> None:
    assert sum(1 for _ in tables(1, 2)) == 5
    assert all(sum(abs(v) for v in t) == 2 and t[0] == t[3] == 0 for t in off_diagonal_tables(2, 2))
    assert sum(1 for _ in off_diagonal_tables(2, 2)) == 8


def test_count_errors() -> None:
    for f in (one_term_count, two_term_count, two_term_count_by_points, two_term_round_count):
        with pytest.raises(ValueError):
            f(-1)
