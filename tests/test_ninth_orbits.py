from __future__ import annotations

from itertools import product
from math import comb

import pytest

from ninth.explore import explore
from ninth.orbits import (
    agreeing_count,
    agreeing_within,
    count_results,
    count_results_part,
    counts_within,
    layer_counts,
    one_term_count,
    one_term_sequences,
    product_count,
    two_term_count,
    two_term_round_count,
)
from ninth.state import DState, canonical, empty


def brute(n: int, total: int) -> int:
    """Well-formed two-relation states with `n` terms and total multiplicity `total`, reduced by rewriting."""
    seen: set[DState] = set()
    slots = n * n
    for r in product(range(total + 1), repeat=slots):
        rest = total - sum(r)
        if rest < 0:
            continue
        for s in product(range(rest + 1), repeat=slots):
            if sum(s) == rest:
                seen.add(canonical(DState(n, r, s)))
    return len(seen)


@pytest.mark.parametrize(("n", "total"), [(0, 0), (0, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1)])
def test_counts_agree_with_listing_every_writing(n: int, total: int) -> None:
    assert count_results(n, total)[total] == brute(n, total)


def test_the_empty_state_and_the_closed_forms() -> None:
    assert count_results(0, 4) == [1, 0, 0, 0, 0] and count_results(1, 4) == [1, 2, 3, 4, 5]
    assert count_results(2, 6) == [1, 4, 20, 60, 170, 396, 868] == [two_term_count(t) for t in range(7)]
    assert all(two_term_count(t) == brute(2, t) for t in range(4))
    assert two_term_count(2) == (comb(9, 7) + comb(4, 3)) // 2 == 20
    assert [two_term_round_count(r) for r in range(8)] == [1, 1, 3, 7, 24, 65, 176, 403]
    assert [one_term_count(t) for t in range(4)] == [1, 2, 3, 4]
    assert one_term_sequences(2, 3) == comb(5, 2) == 10
    assert agreeing_count(2, 0) == 1 and agreeing_count(2, 1) == 0 and agreeing_count(2, 2) == count_results_part(2, 1)[1]
    assert product_count(0, 2) == count_results(0, 2)
    assert product_count(1, 4) == count_results(1, 4)
    assert count_results(2, 2)[2] == 20 > product_count(2, 2)[2] == 16
    with pytest.raises(ValueError):
        count_results(-1, 2)
    with pytest.raises(ValueError):
        count_results(1, -1)
    with pytest.raises(ValueError):
        two_term_count(-1)
    with pytest.raises(ValueError):
        two_term_round_count(-1)
    with pytest.raises(ValueError):
        one_term_count(-1)
    with pytest.raises(ValueError):
        one_term_sequences(-1, 0)
    with pytest.raises(ValueError):
        agreeing_count(-1, 0)


def test_layer_counts_and_counts_within_certify_an_exploration() -> None:
    assert layer_counts(6) == [1, 1, 3, 8, 29, 104, 420]
    expl = explore(empty(), 3, 6)
    by_key: dict[str, int] = {}
    for s in expl.depth:
        by_key[f"{s.n}/{s.m}"] = by_key.get(f"{s.n}/{s.m}", 0) + 1
    assert by_key == counts_within(3, 6)
    assert sum(counts_within(3, 6).values()) == 518
    assert counts_within(5, 2) == {"0/0": 1, "1/0": 1, "1/1": 2, "2/0": 1}
    assert expl.new_per_round[:4] == layer_counts(3)
    two = explore(empty(), 2, 7)
    assert sum(two.new_per_round) == sum(counts_within(2, 7).values()) == sum(two_term_round_count(r) for r in range(8))
    assert agreeing_within(2, 4) == sum(agreeing_count(n, t) for n in range(3) for t in range(5 - n))
