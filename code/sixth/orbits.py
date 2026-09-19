"""Counting the results of the sixth seed without listing them.

Computed.  Every well-formed counted state with at least one term is a result
(a theorem of the paper), `xrx` included, so the results with `n` terms are
counted by the orbit method with the rewriting acting on *all* `n²` ordered
pairs: the earlier derivations' cycles of off-diagonal pairs plus, for every
cycle of the rewriting of length `p`, one cycle of length `p` of diagonal
pairs (`diag_cycles`).  Each cycle contributes the fourth derivation's series
`1 / (1 − x^L)` by total multiplicity; a diagonal cycle may instead be capped
(`1 + x^L + … + x^{cL}`, every `xrx` on it asserted at most `c` times), which
gives the counts by the largest `xrx` multiplicity that the destroyed givens
depend on, and with `c = 0` the fifth derivation's counts of states asserting
no `xrx` (compared in `counts.csv`).

With names (ANCHORED): the first derivation's kinds for the names apart —
neither given asserted; `arb` only; `bra` only; both — and the names one
term split by how often `crc` is asserted at the named term (not at all,
once, twice or more), since the destroyed givens are `m0 + 1 − min(M(c,c),
m0)` (`NAMED_KINDS`, `lost_of_kind`).  Without names (FREE): the least over
placements, by the series for "some pair asserted both ways", "some `xry`
with `x ≠ y` asserted", "every `xrx` asserted fewer than `m` times"
(`counts_by_lost`).  The cost of a result being its size minus that of what
is given plus twice its destroyed givens, the number of results of each
round follows (`layer_counts`), and the results within a bound on terms and
rounds are counted by (terms, total, destroyed givens) as the completeness
certificate.

Cited from the first, fourth and fifth derivations (`xry.orbits`,
`fourth.orbits`, `fifth.orbits`) and re-checked
    `partitions`, `class_size`, `pair_cycles` (the off-diagonal cycles) and
    `series` mention no legality and survive; the fifth's `counts_by_lost` is
    the diagonal-free part of this module's and is imported for the
    comparison (`counts_by_lost_fifth`).
"""

from __future__ import annotations

from math import factorial

from fifth.orbits import counts_by_lost as counts_by_lost_fifth
from fourth.orbits import series
from xry.orbits import class_size, pair_cycles, partitions
from xry.state import Sameness

__all__ = [
    "APART_KINDS",
    "MERGED_KINDS",
    "NAMED_KINDS",
    "count_free",
    "count_named",
    "counts_by_lost",
    "counts_by_lost_fifth",
    "counts_upto",
    "diag_cycles",
    "layer_counts",
    "lost_of_kind",
]

#: How the named terms can stand: apart (the first derivation's four kinds) …
APART_KINDS = ("neither", "arb only", "bra only", "arb and bra")
#: … or one term, by how often `crc` is asserted at it.
MERGED_KINDS = ("one term, crc not asserted", "one term, crc once", "one term, crc twice or more")
NAMED_KINDS = MERGED_KINDS + APART_KINDS

#: Destroyed givens by kind, without and with `bra` given: apart as the first derivation's;
#: one term `m0 + 1 − min(M(c,c), m0)`.
_LOST = {
    False: {
        "one term, crc not asserted": 2,
        "one term, crc once": 1,
        "one term, crc twice or more": 1,
        "neither": 1,
        "arb only": 0,
        "bra only": 1,
        "arb and bra": 0,
    },
    True: {
        "one term, crc not asserted": 3,
        "one term, crc once": 2,
        "one term, crc twice or more": 1,
        "neither": 2,
        "arb only": 1,
        "bra only": 1,
        "arb and bra": 0,
    },
}


def lost_of_kind(bra: bool, kind: str) -> int:
    """The destroyed givens of a state whose names stand as `kind`."""
    return _LOST[bra][kind]


def diag_cycles(parts: tuple[int, ...]) -> dict[int, int]:
    """Cycle lengths (with multiplicity) of the diagonal pairs `(x, x)` under a rewriting.

    A cycle of the rewriting of length `p` carries its `p` diagonal pairs
    around in one cycle of length `p`.
    """
    out: dict[int, int] = {}
    for p in parts:
        out[p] = out.get(p, 0) + 1
    return out


def _averaged(total: list[int], n: int) -> list[int]:
    order = factorial(n)
    if any(c % order for c in total):
        raise ArithmeticError("an orbit count is a whole number")
    return [c // order for c in total]


def _times_geometric(poly: list[int], length: int, degree: int) -> None:
    """Multiply by `1 / (1 − x**length)`, in place."""
    for i in range(length, degree + 1):
        poly[i] += poly[i - length]


def _times_capped(poly: list[int], length: int, cap: int, degree: int) -> list[int]:
    """Multiply by `1 + x**length + … + x**(cap * length)`."""
    out = [0] * (degree + 1)
    for i in range(degree + 1):
        for k in range(cap + 1):
            if i - k * length < 0:
                break
            out[i] += poly[i - k * length]
    return out


def _with_diagonal(poly: list[int], diag: dict[int, int], cap: int | None, degree: int) -> list[int]:
    """`poly` times the factor of every diagonal cycle in `diag` (geometric, or capped at `cap`)."""
    acc = list(poly)
    for length, count in sorted(diag.items()):
        for _ in range(count):
            if cap is None:
                _times_geometric(acc, length, degree)
            else:
                acc = _times_capped(acc, length, cap, degree)
    return acc


def _unchanged(parts: tuple[int, ...], degree: int, one_way: bool, cap: int | None, off: bool) -> list[int]:
    """States left unchanged by a rewriting of cycle type `parts`, by total multiplicity.

    `one_way`: no pair asserted both ways; `off=False`: nothing off-diagonal
    asserted; `cap`: every `xrx` asserted at most `cap` times.
    """
    if off:
        poly = series(pair_cycles(parts, one_way), degree, both_ways_excluded=one_way)
    else:
        poly = [1] + [0] * degree
    return _with_diagonal(poly, diag_cycles(parts), cap, degree)


def count_free(n: int, degree: int, one_way: bool = False, cap: int | None = None, off: bool = True) -> list[int]:
    """States with `n` terms up to any rewriting, by total multiplicity `0..degree`.

    Optionally restricted to no pair asserted both ways (`one_way`), nothing
    off-diagonal asserted (`off=False`), every `xrx` at most `cap` times.
    """
    total = [0] * (degree + 1)
    for parts in partitions(n):
        size = class_size(parts)
        for t, c in enumerate(_unchanged(parts, degree, one_way, cap, off)):
            total[t] += size * c
    return _averaged(total, n)


def _shifted(rest: list[int], shift: int, degree: int) -> list[int]:
    """`rest` times `x**shift / (1 - x)**shift`: each of `shift` pairs asserted at least once."""
    acc = list(rest)
    for _ in range(shift):
        for i in range(1, degree + 1):
            acc[i] += acc[i - 1]
    return [0] * shift + acc[: degree + 1 - shift]


def _exactly(rest: list[int], k: int, degree: int) -> list[int]:
    """`rest` times `x**k`: one pair asserted exactly `k` times."""
    return [0] * k + rest[: degree + 1 - k]


def _at_least(rest: list[int], k: int, cap: int | None, degree: int) -> list[int]:
    """`rest` times `x**k + x**(k+1) + …` (up to `x**cap` when capped): one pair asserted `k` times or more."""
    if cap is None:
        acc = list(rest)
        for i in range(1, degree + 1):
            acc[i] += acc[i - 1]
        return [0] * k + acc[: degree + 1 - k]
    out = [0] * (degree + 1)
    for j in range(k, cap + 1):
        for i, c in enumerate(_exactly(rest, j, degree)):
            out[i] += c
    return out


def count_named(n: int, degree: int, cap: int | None = None) -> dict[str, list[int]]:
    """States with `n` terms and names, up to rewritings keeping the names, by kind and total.

    A rewriting keeps the names only if it fixes the named terms; the pairs it
    fixes among `ab`, `ba`, `aa`, `bb` (or `cc`) are then cycles of length one
    handled apart.  `cap` bounds every `xrx` multiplicity (`0`: the fifth
    derivation's states).
    """
    total = {kind: [0] * (degree + 1) for kind in NAMED_KINDS}
    for parts in partitions(n):
        size = class_size(parts)
        kept = parts.count(1)
        off = pair_cycles(parts, False)
        diag = diag_cycles(parts)
        if kept >= 1:
            # The names on one term `c`: every cycle but `(c, c)`.
            others_diag = dict(diag)
            others_diag[1] -= 1
            rest = _with_diagonal(series(off, degree), others_diag, cap, degree)
            ways = size * kept
            for t, c in enumerate(_exactly(rest, 0, degree)):
                total["one term, crc not asserted"][t] += ways * c
            if cap is None or cap >= 1:
                for t, c in enumerate(_exactly(rest, 1, degree)):
                    total["one term, crc once"][t] += ways * c
            for t, c in enumerate(_at_least(rest, 2, cap, degree)):
                total["one term, crc twice or more"][t] += ways * c
        if kept < 2:
            continue
        # The names on two terms: every off-diagonal cycle but `ab`, `ba`; every diagonal cycle.
        others_off = dict(off)
        others_off[1] -= 2
        rest = _with_diagonal(series(others_off, degree), diag, cap, degree)
        ways = size * kept * (kept - 1)
        for kind, between in (("neither", 0), ("arb only", 1), ("bra only", 1), ("arb and bra", 2)):
            for t, c in enumerate(_shifted(rest, between, degree)):
                total[kind][t] += ways * c
    return {kind: _averaged(counts, n) for kind, counts in total.items()}


def counts_by_lost(sameness: Sameness, bra: bool, n: int, degree: int, cap: int | None = None) -> dict[int, list[int]]:
    """Results with `n` terms by destroyed givens, then by total multiplicity `0..degree`.

    `cap` bounds every `xrx` multiplicity; with `cap = 0` this is the fifth
    derivation's count.
    """
    m0 = 2 if bra else 1
    out: dict[int, list[int]] = {}

    def put(value: int, counts: list[int]) -> None:
        acc = out.setdefault(value, [0] * (degree + 1))
        for t, c in enumerate(counts):
            acc[t] += c

    if sameness is Sameness.ANCHORED:
        for kind, counts in count_named(n, degree, cap).items():
            put(_LOST[bra][kind], counts)
        return out
    every = count_free(n, degree, cap=cap)
    if n == 1:
        # One term `c` asserting `crc` `t` times: the names on it, `lost = m0 + 1 − min(t, m0)`.
        for t, c in enumerate(every):
            put(m0 + 1 - min(t, m0), [c if i == t else 0 for i in range(degree + 1)])
        return out
    only_diag = count_free(n, degree, cap=cap, off=False)
    if not bra:
        put(0, [e - d for e, d in zip(every, only_diag)])
        put(1, only_diag)
        return out
    one_way = count_free(n, degree, one_way=True, cap=cap)
    below_two = count_free(n, degree, cap=1 if cap is None else min(cap, 1), off=False)
    put(0, [e - o for e, o in zip(every, one_way)])
    put(1, [o - d for o, d in zip(one_way, below_two)])
    put(2, below_two)
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
    multiplicity at most `k + 3`.
    """
    size0 = 2 + (2 if bra else 1)
    layers = [0] * (upto + 1)
    for n in range(1, upto + 3):
        for value, counts in counts_by_lost(sameness, bra, n, upto + 4).items():
            for t, count in enumerate(counts):
                k = n + t - size0 + 2 * value
                if 0 <= k <= upto:
                    layers[k] += count
    return layers
