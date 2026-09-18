from __future__ import annotations

from itertools import product

import pytest

from fourth.cost import cost_free, has_two_way
from fourth.explore import explore
from fourth.orbits import count_results, count_simple, counts_upto, layer_counts, series
from fourth.orbits import _averaged
from fourth.state import MState, canonical, given
from second.orbits import count_results as count_results_third
from xry.state import Sameness


def brute(sameness: Sameness, bra: bool, n: int, total: int) -> int:
    """Results with `n` terms and total multiplicity `total`, by listing every writing."""
    if n < 2 and sameness is Sameness.ANCHORED:
        return 0
    cells = [(x, y) for x in range(n) for y in range(n) if x != y]
    seen: set[MState] = set()
    for split in product(range(total + 1), repeat=len(cells)):
        if sum(split) != total:
            continue
        mult = [0] * (n * n)
        for (x, y), k in zip(cells, split):
            mult[x * n + y] = k
        if sameness is Sameness.ANCHORED:
            state = MState(n, tuple(mult), (0, 1))
            if not state.has(0, 1) or (bra and not state.has(1, 0)):
                continue
        else:
            state = MState(n, tuple(mult))
            if not (has_two_way(state) if bra else state.m > 0):
                continue
        seen.add(canonical(state))
    return len(seen)


@pytest.mark.parametrize("sameness", list(Sameness))
@pytest.mark.parametrize("bra", [False, True])
def test_counts_agree_with_listing(sameness: Sameness, bra: bool) -> None:
    for n, upto in ((1, 3), (2, 6), (3, 4), (4, 3)):
        counted = counts_upto(sameness, bra, n, upto)
        assert counted == [brute(sameness, bra, n, t) for t in range(upto + 1)]
        assert count_results(sameness, bra, n, upto) == counted[upto]


def test_two_term_counts_in_closed_form() -> None:
    upto = 12
    assert counts_upto(Sameness.ANCHORED, False, 2, upto) == [t for t in range(upto + 1)]
    assert counts_upto(Sameness.ANCHORED, True, 2, upto) == [max(t - 1, 0) for t in range(upto + 1)]
    assert counts_upto(Sameness.FREE, False, 2, upto) == [0] + [t // 2 + 1 for t in range(1, upto + 1)]
    assert counts_upto(Sameness.FREE, True, 2, upto) == [0, 0] + [(t - 2) // 2 + 1 for t in range(2, upto + 1)]


def test_the_results_asserting_nothing_twice_are_the_third_derivations_counts() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            for n in range(1, 5):
                simple = count_simple(sameness, bra, n, 14)
                assert simple[: n * (n - 1) + 1] == count_results_third(sameness, bra, n)
                assert simple[n * (n - 1) + 1 :] == [0] * (14 - n * (n - 1))
                assert all(s <= c for s, c in zip(simple, counts_upto(sameness, bra, n, 14)))
    assert count_simple(Sameness.FREE, False, 3, 2) == [0, 1, 4]


def test_layer_counts_agree_with_the_exploration() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            layers = layer_counts(sameness, bra, 5)
            assert layers[0] == 1
            expl = explore(given(bra, sameness), 7, rounds=3)
            assert expl.new_per_round == layers[:4]
    assert layer_counts(Sameness.ANCHORED, False, 3) == [1, 3, 10, 33]
    assert layer_counts(Sameness.FREE, False, 2) == [1, 3, 8]


def test_series() -> None:
    assert series({}, 4) == [1, 0, 0, 0, 0]
    assert series({1: 1}, 4) == [1, 1, 1, 1, 1]
    assert series({1: 2}, 4) == [1, 2, 3, 4, 5]
    assert series({2: 1}, 5) == [1, 0, 1, 0, 1, 0]
    assert series({2: 1}, 6, both_ways_excluded=True) == [1, 0, 2, 0, 2, 0, 2]
    assert series({1: 1, 2: 1}, 4) == [1, 1, 2, 2, 3]
    with pytest.raises(ArithmeticError):
        _averaged([1], 2)


def test_free_counts_are_the_free_cost_results() -> None:
    for bra in (False, True):
        seen: set[MState] = set()
        for mult in product(range(4), repeat=4):
            state = MState(2, mult)
            if state.legal and cost_free(state, bra) is not None and state.m <= 3:
                seen.add(canonical(state))
        assert len(seen) == sum(counts_upto(Sameness.FREE, bra, 2, 3))
