from __future__ import annotations

from itertools import product

import pytest

from fifth.orbits import count_free_all as count_free_fifth
from fifth.orbits import count_named as count_named_fifth
from sixth.explore import explore
from sixth.orbits import (
    APART_KINDS,
    MERGED_KINDS,
    NAMED_KINDS,
    _averaged,
    count_free,
    count_named,
    counts_by_lost,
    counts_by_lost_fifth,
    counts_upto,
    diag_cycles,
    layer_counts,
    lost_of_kind,
)
from sixth.state import MState, canonical, given
from xry.state import Sameness


def vectors(n: int, total: int) -> list[tuple[int, ...]]:
    """Every multiplicity vector on the `n²` pairs with the given total."""
    return [split for split in product(range(total + 1), repeat=n * n) if sum(split) == total]


def kind_of(state: MState) -> str:
    assert state.names is not None
    a, b = state.names
    if a == b:
        k = state.mult_of(a, a)
        return MERGED_KINDS[min(k, 2)]
    if state.has(a, b) and state.has(b, a):
        return "arb and bra"
    if state.has(a, b):
        return "arb only"
    if state.has(b, a):
        return "bra only"
    return "neither"


def brute_named(n: int, total: int, cap: int | None) -> dict[str, int]:
    seen: dict[str, set[MState]] = {kind: set() for kind in NAMED_KINDS}
    for mult in vectors(n, total):
        state = MState(n, mult)
        if cap is not None and any(state.mult_of(x, x) > cap for x in range(n)):
            continue
        for a in range(n):
            for b in range(n):
                named = MState(n, mult, (a, b))
                seen[kind_of(named)].add(canonical(named))
    return {kind: len(v) for kind, v in seen.items()}


def brute_free(n: int, total: int, one_way: bool = False, cap: int | None = None, off: bool = True) -> int:
    seen: set[MState] = set()
    for mult in vectors(n, total):
        state = MState(n, mult)
        pairs = state.pairs
        if one_way and any(x != y and state.has(y, x) for x, y in pairs):
            continue
        if cap is not None and any(state.mult_of(x, x) > cap for x in range(n)):
            continue
        if not off and any(x != y for x, y in pairs):
            continue
        seen.add(canonical(state))
    return len(seen)


def test_counts_agree_with_listing() -> None:
    for n, upto in ((1, 4), (2, 4), (3, 3)):
        for cap in (None, 0, 1, 2):  # cap>=2 exercises _at_least's capped "k or more" loop
            named = count_named(n, upto, cap)
            for t in range(upto + 1):
                assert {kind: named[kind][t] for kind in NAMED_KINDS} == brute_named(n, t, cap), (n, t, cap)
                assert count_free(n, upto, cap=cap)[t] == brute_free(n, t, cap=cap)
                assert count_free(n, upto, one_way=True, cap=cap)[t] == brute_free(n, t, one_way=True, cap=cap)
                assert count_free(n, upto, off=False, cap=cap)[t] == brute_free(n, t, off=False, cap=cap)
    assert diag_cycles((2, 1, 1)) == {2: 1, 1: 2}
    assert count_free(1, 3) == [1, 1, 1, 1] and count_free(1, 3, cap=1) == [1, 1, 0, 0]
    assert count_named(1, 2) == {
        "one term, crc not asserted": [1, 0, 0], "one term, crc once": [0, 1, 0], "one term, crc twice or more": [0, 0, 1],
        "neither": [0, 0, 0], "arb only": [0, 0, 0], "bra only": [0, 0, 0], "arb and bra": [0, 0, 0],
    }  # fmt: skip


def test_the_xrx_free_part_is_the_fifth_derivations_count() -> None:
    for n in range(1, 5):
        assert count_free(n, 8, cap=0) == count_free_fifth(n, 8)
        legal = count_named(n, 8, cap=0)
        theirs = count_named_fifth(n, 8)
        assert legal["one term, crc not asserted"] == theirs["a and b one term"]
        assert all(legal[kind] == theirs[kind] for kind in APART_KINDS)
        assert legal["one term, crc once"] == [0] * 9 == legal["one term, crc twice or more"]
        for sameness in Sameness:
            for bra in (False, True):
                ours = {k: v for k, v in counts_by_lost(sameness, bra, n, 8, cap=0).items() if any(v)}
                fifth = {k: v for k, v in counts_by_lost_fifth(sameness, bra, n, 8).items() if any(v)}
                assert ours == fifth, (sameness, bra, n)


def test_counts_by_destroyed_givens() -> None:
    assert lost_of_kind(False, "neither") == 1 and lost_of_kind(True, "one term, crc twice or more") == 1
    assert lost_of_kind(True, "one term, crc once") == 2 and lost_of_kind(False, "one term, crc once") == 1
    assert counts_by_lost(Sameness.FREE, False, 1, 3) == {2: [1, 0, 0, 0], 1: [0, 1, 1, 1]}
    assert counts_by_lost(Sameness.FREE, True, 1, 3) == {3: [1, 0, 0, 0], 2: [0, 1, 0, 0], 1: [0, 0, 1, 1]}
    two = counts_by_lost(Sameness.FREE, False, 2, 3)
    assert two[1] == [1, 1, 2, 2] and two[0][0] == 0 and sum(two[0]) + sum(two[1]) == sum(count_free(2, 3))
    both = counts_by_lost(Sameness.FREE, True, 2, 3)
    assert both[2] == [1, 1, 1, 0] and both[1][0] == 0 and both[0][:2] == [0, 0]
    for sameness in Sameness:
        for bra in (False, True):
            for n in range(1, 4):
                by_lost = counts_by_lost(sameness, bra, n, 6)
                assert counts_upto(sameness, bra, n, 6) == [sum(v[t] for v in by_lost.values()) for t in range(7)]
                assert set(by_lost) <= {0, 1, 2, 3}
                # Every state is counted exactly once: the total equals the count of all states.
                total = count_free(n, 6) if sameness is Sameness.FREE else [
                    sum(v[t] for v in count_named(n, 6).values()) for t in range(7)
                ]
                assert counts_upto(sameness, bra, n, 6) == total


def test_layer_counts_agree_with_the_exploration() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            layers = layer_counts(sameness, bra, 4)
            assert layers[0] == 1
            expl = explore(given(bra, sameness), 5, rounds=3)
            assert expl.new_per_round == layers[:4], (sameness, bra)
    assert layer_counts(Sameness.ANCHORED, False, 1) == [1, 7]
    assert layer_counts(Sameness.FREE, False, 1) == [1, 7]


def test_averaging_refuses_a_fraction() -> None:
    with pytest.raises(ArithmeticError):
        _averaged([1], 2)
