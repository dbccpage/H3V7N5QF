from __future__ import annotations

from itertools import product

import pytest

from eighth.cost import destroyed
from eighth.explore import explore
from eighth.orbits import (
    NAMED_KINDS,
    count_free,
    count_named,
    counts_by_lost,
    counts_upto,
    counts_within,
    layer_counts,
    lost_of_kind,
    product_count,
    two_term_round_count,
)
from eighth.state import DState, canonical, given
from sixth.orbits import count_free as count_free_part
from xry.state import Sameness


def brute_free(n: int, total: int) -> int:
    seen: set[DState] = set()
    for r in product(range(total + 1), repeat=n * n):
        rest = total - sum(r)
        if rest < 0:
            continue
        for s in product(range(rest + 1), repeat=n * n):
            if sum(s) == rest:
                seen.add(canonical(DState(n, r, s)))
    return len(seen)


def kind_of(state: DState) -> str:
    assert state.names is not None
    a, b = state.names
    part = state.r_part()
    if a == b:
        k = part.mult_of(a, a)
        return ("one term, crc not asserted", "one term, crc once", "one term, crc twice or more")[min(k, 2)]
    if part.has(a, b) and part.has(b, a):
        return "arb and bra"
    if part.has(a, b):
        return "arb only"
    if part.has(b, a):
        return "bra only"
    return "neither"


def brute_named(n: int, total: int) -> dict[str, int]:
    seen: dict[str, set[DState]] = {kind: set() for kind in NAMED_KINDS}
    for r in product(range(total + 1), repeat=n * n):
        rest = total - sum(r)
        if rest < 0:
            continue
        for s in product(range(rest + 1), repeat=n * n):
            if sum(s) != rest:
                continue
            for a in range(n):
                for b in range(n):
                    state = canonical(DState(n, r, s, (a, b)))
                    seen[kind_of(state)].add(state)
    return {kind: len(v) for kind, v in seen.items()}


@pytest.mark.parametrize(("n", "total"), [(1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2)])
def test_counts_agree_with_listing_every_writing(n: int, total: int) -> None:
    assert count_free(n, total)[total] == brute_free(n, total)
    named = count_named(n, max(total, 2))  # the sixth's capped helper wants a degree of at least two
    assert {kind: named[kind][total] for kind in NAMED_KINDS} == brute_named(n, total)


def test_the_count_is_not_a_product_beyond_one_term() -> None:
    assert count_free(1, 4) == product_count(1, 4) == [1, 2, 3, 4, 5]
    assert count_free(2, 4) == [1, 4, 20, 60, 170] and product_count(2, 4) == [1, 4, 16, 44, 114]
    assert count_free(2, 2)[2] == 20 > product_count(2, 2)[2] == 16
    assert count_free_part(2, 4) == [1, 2, 6, 10, 19]
    assert lost_of_kind(False, "neither") == 1
    capped = count_named(2, 3, cap=0)
    assert capped["one term, crc once"] == [0, 0, 0, 0] and capped["one term, crc not asserted"] == [1, 6, 21, 56]


def test_counts_by_lost_and_layers_certify_an_exploration() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            expl = explore(given(bra, sameness), 3, 4)
            by: dict[str, int] = {}
            for s in expl.depth:
                key = f"{s.n}/{s.m}/{destroyed(s, bra)}"
                by[key] = by.get(key, 0) + 1
            assert by == counts_within(sameness, bra, 3, 4)
            assert expl.new_per_round[:2] == layer_counts(sameness, bra, 1)
            assert sum(counts_upto(sameness, bra, 2, 3)) == sum(sum(v) for v in counts_by_lost(sameness, bra, 2, 3).values())
    assert layer_counts(Sameness.ANCHORED, False, 4) == [1, 11, 67, 372, 2096]
    assert layer_counts(Sameness.FREE, False, 4) == [1, 11, 57, 277, 1345]
    one = counts_by_lost(Sameness.FREE, True, 1, 3, cap=1)
    assert sum(sum(v) for v in one.values()) == 1 + 2 + 2 + 2  # t_r at most 1
    assert sum(two_term_round_count(False, r) for r in range(5)) == sum(counts_within(Sameness.ANCHORED, False, 2, 4).values())
