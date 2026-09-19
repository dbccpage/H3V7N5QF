from __future__ import annotations

from itertools import product

import pytest

from fifth.explore import explore
from fifth.orbits import (
    NAMED_KINDS,
    _averaged,
    count_free_all,
    count_named,
    count_one_way,
    counts_by_lost,
    counts_upto,
    counts_upto_fourth,
    layer_counts,
    lost_of_kind,
)
from fifth.state import MState, canonical, given
from xry.orbits import count_free as count_free_simple
from xry.orbits import count_named as count_named_simple
from xry.orbits import count_one_way as count_one_way_simple
from xry.state import Sameness


def brute_named(n: int, total: int) -> dict[str, int]:
    """Legal states with `n` terms and total `total`, by how the names stand, by listing every writing."""
    cells = [(x, y) for x in range(n) for y in range(n) if x != y]
    seen: dict[str, set[MState]] = {kind: set() for kind in NAMED_KINDS}
    for split in product(range(total + 1), repeat=len(cells)):
        if sum(split) != total:
            continue
        mult = [0] * (n * n)
        for (x, y), k in zip(cells, split):
            mult[x * n + y] = k
        for a in range(n):
            for b in range(n):
                state = MState(n, tuple(mult), (a, b))
                if a == b:
                    kind = "a and b one term"
                elif state.has(a, b) and state.has(b, a):
                    kind = "arb and bra"
                elif state.has(a, b):
                    kind = "arb only"
                elif state.has(b, a):
                    kind = "bra only"
                else:
                    kind = "neither"
                seen[kind].add(canonical(state))
    return {kind: len(v) for kind, v in seen.items()}


def brute_free(n: int, total: int, one_way: bool) -> int:
    cells = [(x, y) for x in range(n) for y in range(n) if x != y]
    seen: set[MState] = set()
    for split in product(range(total + 1), repeat=len(cells)):
        if sum(split) != total:
            continue
        mult = [0] * (n * n)
        for (x, y), k in zip(cells, split):
            mult[x * n + y] = k
        state = MState(n, tuple(mult))
        if one_way and any(state.has(y, x) for x, y in state.pairs):
            continue
        seen.add(canonical(state))
    return len(seen)


def test_counts_agree_with_listing() -> None:
    for n, upto in ((1, 3), (2, 5), (3, 3)):
        named = count_named(n, upto)
        free_all = count_free_all(n, upto)
        one_way = count_one_way(n, upto)
        for t in range(upto + 1):
            assert {kind: named[kind][t] for kind in NAMED_KINDS} == brute_named(n, t), (n, t)
            assert free_all[t] == brute_free(n, t, False) and one_way[t] == brute_free(n, t, True)


def test_the_states_asserting_nothing_twice_are_the_first_derivations_counts() -> None:
    for n in range(1, 5):
        named = count_named(n, 14)
        simple = count_named_simple(n)
        assert all(named[kind][t] >= c for kind in NAMED_KINDS for t, c in enumerate(simple[kind]))
        assert count_free_all(n, 14)[: n * (n - 1) + 1] >= count_free_simple(n)
        assert count_one_way(n, 14)[: n * (n - 1) + 1] >= count_one_way_simple(n)
    assert count_named(2, 3)["arb only"] == [0, 1, 1, 1]
    assert count_named(2, 3)["arb and bra"] == [0, 0, 1, 2]
    assert count_named(2, 3)["a and b one term"] == [1, 2, 3, 4]
    assert count_named(1, 2) == {"a and b one term": [1, 0, 0], "neither": [0, 0, 0], "arb only": [0, 0, 0], "bra only": [0, 0, 0], "arb and bra": [0, 0, 0]}


def test_the_fourth_derivations_counts_are_the_lost_zero_part() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            for n in range(1, 5):
                by_lost = counts_by_lost(sameness, bra, n, 8)
                assert by_lost.get(0, [0] * 9) == counts_upto_fourth(sameness, bra, n, 8)
                assert counts_upto(sameness, bra, n, 8) == [sum(v[t] for v in by_lost.values()) for t in range(9)]
                assert set(by_lost) <= {0, 1, 2, 3}
    assert lost_of_kind(False, "neither") == 1 and lost_of_kind(True, "a and b one term") == 3
    assert counts_by_lost(Sameness.FREE, False, 1, 3) == {2: [1, 0, 0, 0]}
    assert counts_by_lost(Sameness.FREE, True, 1, 3) == {3: [1, 0, 0, 0]}
    assert counts_by_lost(Sameness.FREE, False, 2, 3) == {1: [1, 0, 0, 0], 0: [0, 1, 2, 2]}
    assert counts_by_lost(Sameness.FREE, True, 2, 3) == {2: [1, 0, 0, 0], 1: [0, 1, 1, 1], 0: [0, 0, 1, 1]}


def test_layer_counts_agree_with_the_exploration() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            layers = layer_counts(sameness, bra, 5)
            assert layers[0] == 1
            expl = explore(given(bra, sameness), 7, rounds=3)
            assert expl.new_per_round == layers[:4]
    assert layer_counts(Sameness.ANCHORED, False, 3) == [1, 4, 13, 41]
    assert layer_counts(Sameness.FREE, False, 2) == [1, 4, 10]


def test_averaging_refuses_a_fraction() -> None:
    with pytest.raises(ArithmeticError):
        _averaged([1], 2)
