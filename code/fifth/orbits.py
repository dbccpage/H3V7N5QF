"""Counting the results of the fifth seed without listing them.

Computed.  Every legal counted state with at least one term is a result (a
theorem of the paper), so the results with `n` terms are counted as the first
derivation counted legal states — by terms and by how the named terms stand
(`NAMED_KINDS`: one term; neither; `arb` only; `bra` only; both) — with the
fourth derivation's series `1 / (1 − x^L)` per cycle of the rewriting's action
on ordered pairs, by total multiplicity.  The cost of a result is its size
minus that of what is given plus twice its destroyed givens (`_LOST` per
kind), so the number of results of each round follows (`layer_counts`), and
the results within a bound on terms and rounds are counted by (terms, total,
lost) as the completeness certificate (`counts_by_lost`).

Cited from the first derivation (`xry.orbits`) and re-checked
    `partitions`, `class_size`, `pair_cycles` and the way the names are
    handled (`count_named`: a rewriting keeps the names only if it fixes the
    named terms; the pairs `ab`, `ba` are then cycles of length one) mention
    no change and survive.  `NAMED_KINDS` and the destroyed givens per kind
    are the first's.

Cited from the fourth derivation (`fourth.orbits`) and re-checked
    `series` (the generating series per cycle, with the one-way variant) is
    about states and survives; `counts_upto` there counts the states
    containing what is given, which are the kinds `arb only` and `arb and
    bra` (names kept) or the positive totals (FREE) here — the lost = 0 part,
    compared in `counts.csv`.
"""

from __future__ import annotations

from math import factorial

from fourth.orbits import counts_upto as counts_upto_fourth
from fourth.orbits import series
from xry.orbits import NAMED_KINDS, class_size, pair_cycles, partitions
from xry.state import Sameness

__all__ = [
    "NAMED_KINDS",
    "count_free_all",
    "count_named",
    "count_one_way",
    "counts_by_lost",
    "counts_upto",
    "counts_upto_fourth",
    "layer_counts",
    "lost_of_kind",
]

#: Destroyed givens by how the named terms stand, without and with `bra` given (the first's).
_LOST = {
    False: {"a and b one term": 2, "neither": 1, "arb only": 0, "bra only": 1, "arb and bra": 0},
    True: {"a and b one term": 3, "neither": 2, "arb only": 1, "bra only": 1, "arb and bra": 0},
}


def lost_of_kind(bra: bool, kind: str) -> int:
    """The destroyed givens of a state whose names stand as `kind`."""
    return _LOST[bra][kind]


def _averaged(total: list[int], n: int) -> list[int]:
    order = factorial(n)
    if any(c % order for c in total):
        raise ArithmeticError("an orbit count is a whole number")
    return [c // order for c in total]


def count_free_all(n: int, degree: int) -> list[int]:
    """Legal states with `n` terms up to any rewriting, by total multiplicity `0..degree`."""
    total = [0] * (degree + 1)
    for parts in partitions(n):
        size = class_size(parts)
        for t, c in enumerate(series(pair_cycles(parts, False), degree)):
            total[t] += size * c
    return _averaged(total, n)


def count_one_way(n: int, degree: int) -> list[int]:
    """As `count_free_all`, keeping only states with no pair asserted both ways."""
    total = [0] * (degree + 1)
    for parts in partitions(n):
        size = class_size(parts)
        for t, c in enumerate(series(pair_cycles(parts, True), degree, both_ways_excluded=True)):
            total[t] += size * c
    return _averaged(total, n)


def _shifted(rest: list[int], shift: int, degree: int) -> list[int]:
    """`rest` times `x**shift / (1 - x)**shift`: each named pair asserted at least once."""
    acc = list(rest)
    for _ in range(shift):
        for i in range(1, degree + 1):
            acc[i] += acc[i - 1]
    return [0] * shift + acc[: degree + 1 - shift]


def count_named(n: int, degree: int) -> dict[str, list[int]]:
    """Legal states with `n` terms and names, up to rewritings keeping the names.

    Split by how `a` and `b` stand to each other, then by total multiplicity.
    """
    total = {kind: [0] * (degree + 1) for kind in NAMED_KINDS}
    for parts in partitions(n):
        size = class_size(parts)
        kept = parts.count(1)
        cycles = pair_cycles(parts, False)
        for t, c in enumerate(series(cycles, degree)):
            total["a and b one term"][t] += size * kept * c
        if kept < 2:
            continue
        others = dict(cycles)
        others[1] -= 2
        rest = series(others, degree)
        ways = size * kept * (kept - 1)
        for kind, between in (("neither", 0), ("arb only", 1), ("bra only", 1), ("arb and bra", 2)):
            for t, c in enumerate(_shifted(rest, between, degree)):
                total[kind][t] += ways * c
    return {kind: _averaged(counts, n) for kind, counts in total.items()}


def counts_by_lost(sameness: Sameness, bra: bool, n: int, degree: int) -> dict[int, list[int]]:
    """Results with `n` terms by destroyed givens, then by total multiplicity `0..degree`."""
    m0 = 2 if bra else 1
    out: dict[int, list[int]] = {}

    def put(value: int, counts: list[int]) -> None:
        acc = out.setdefault(value, [0] * (degree + 1))
        for t, c in enumerate(counts):
            acc[t] += c

    if sameness is Sameness.ANCHORED:
        for kind, counts in count_named(n, degree).items():
            put(_LOST[bra][kind], counts)
        return out
    every = count_free_all(n, degree)
    if n == 1:
        put(1 + m0, every)
        return out
    put(m0, [every[0]] + [0] * degree)
    if bra:
        one_way = count_one_way(n, degree)
        put(1, [0] + one_way[1:])
        put(0, [0] + [c - o for c, o in zip(every[1:], one_way[1:])])
    else:
        put(0, [0] + every[1:])
    return out


def counts_upto(sameness: Sameness, bra: bool, n: int, degree: int) -> list[int]:
    """Results with `n` terms by total multiplicity `0..degree` (all destroyed-given values)."""
    total = [0] * (degree + 1)
    for counts in counts_by_lost(sameness, bra, n, degree).values():
        for t, c in enumerate(counts):
            total[t] += c
    return total


def layer_counts(sameness: Sameness, bra: bool, upto: int) -> list[int]:
    """How many results need exactly `k` changes, for `k = 0..upto`, with no bound.

    A result needing `k` changes has at most `k + 2` terms and total
    multiplicity at most `k + 2`.
    """
    size0 = 2 + (2 if bra else 1)
    layers = [0] * (upto + 1)
    for n in range(1, upto + 3):
        for value, counts in counts_by_lost(sameness, bra, n, upto + 2).items():
            for t, count in enumerate(counts):
                k = n + t - size0 + 2 * value
                if 0 <= k <= upto:
                    layers[k] += count
    return layers
