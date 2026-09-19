from __future__ import annotations

from itertools import product
from math import comb

import pytest

from seventh.explore import explore
from seventh.orbits import count_results, counts_within, layer_counts, two_term_count, two_term_round_count
from seventh.state import MState, canonical, empty


def brute(n: int, total: int) -> int:
    """Well-formed states with `n` terms and total multiplicity `total`, listed and reduced by rewriting."""
    seen: set[MState] = set()
    for mult in product(range(total + 1), repeat=n * n):
        if sum(mult) == total:
            seen.add(canonical(MState(n, mult)))
    return len(seen)


@pytest.mark.parametrize(("n", "total"), [(0, 0), (0, 2), (1, 3), (2, 0), (2, 1), (2, 3), (2, 4), (3, 2), (3, 3)])
def test_counts_agree_with_listing_every_writing(n: int, total: int) -> None:
    assert count_results(n, total)[total] == brute(n, total)


def test_the_empty_state_and_the_closed_forms() -> None:
    assert count_results(0, 4) == [1, 0, 0, 0, 0] and count_results(1, 4) == [1] * 5
    assert count_results(2, 6) == [1, 2, 6, 10, 19, 28, 44] == [two_term_count(t) for t in range(7)]
    assert all(two_term_count(t) == brute(2, t) for t in range(6))
    assert two_term_count(4) == (comb(7, 3) + 3) // 2 == 19
    assert [two_term_round_count(r) for r in range(12)] == [1, 1, 2, 3, 7, 11, 20, 29, 45, 61, 86, 111]
    with pytest.raises(ValueError):
        count_results(-1, 2)
    with pytest.raises(ValueError):
        count_results(1, -1)
    with pytest.raises(ValueError):
        two_term_count(-1)
    with pytest.raises(ValueError):
        two_term_round_count(-1)


def test_layer_counts_and_counts_within_certify_an_exploration() -> None:
    assert layer_counts(6) == [1, 1, 2, 4, 10, 24, 65]
    expl = explore(empty(), 3, 6)
    by_key: dict[str, int] = {}
    for s in expl.depth:
        by_key[f"{s.n}/{s.m}"] = by_key.get(f"{s.n}/{s.m}", 0) + 1
    assert by_key == counts_within(3, 6)
    assert sum(counts_within(3, 6).values()) == 89 and counts_within(5, 2) == {"0/0": 1, "1/0": 1, "1/1": 1, "2/0": 1}
    assert expl.new_per_round[:4] == layer_counts(3)
    two = explore(empty(), 2, 9)
    assert sum(two.new_per_round) == sum(counts_within(2, 9).values()) == sum(two_term_round_count(r) for r in range(10))
