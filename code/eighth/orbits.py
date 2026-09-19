"""Counting the results of the eighth seed without listing them.

Computed.  Every well-formed two-relation state with at least one term is a
result (a theorem of the paper), so the results with `n` terms are counted by
the orbit method with the rewriting acting on all `n²` ordered pairs *twice*
— once for each relation.  A rewriting leaves a state unchanged exactly when
each relation's multiplicity is the same all along each cycle of pairs; so
every cycle of length `L` (off-diagonal or diagonal, `sixth.orbits`)
contributes the series `1 / (1 − x^L)` once for `r` and once for `s`.  The
destroyed givens depend on the `r` part alone, so the `r` factor is the
sixth's (by kind of the named terms, capped where the largest `xrx`
multiplicity matters) and the `s` factor is free (`_s_factor`).  The
results within a bound on terms and rounds are counted by (terms, total,
destroyed givens) as the completeness certificate (`counts_within`).

The number of results with `n ≥ 2` terms is *not* the product of the
single-relation counts (`product_count`): the rewriting acts on both
relations at once, so two states that are the same relation by relation up
to separate rewritings may differ up to one rewriting.  With one term the two
agree.

Cited from the fourth, sixth and seventh derivations (`fourth.orbits`,
`sixth.orbits`) and re-checked
    `series`, `partitions`, `class_size`, `pair_cycles`, `diag_cycles` and
    the sixth's helpers on one multiplicity function (`_unchanged`,
    `_with_diagonal`, `_shifted`, `_exactly`, `_at_least`, `_averaged`,
    `lost_of_kind`, the kinds) mention no second relation and survive: each
    is applied to the `r` part and multiplied by the `s` factor.  The sixth's
    `count_free` (imported as `count_free_part`) is the count of one relation
    and gives the product and the `s` factor's check.

Derived (paper)
    With two terms, names kept, the results of round `r` are the sixth's
    two-term kinds of round `k` convolved with the `s` states on the same
    terms of total `r − k` (`C(r − k + 3, 3)` with the names apart or one
    term with a second term; one for each total on one term):
    `two_term_round_count`.
"""

from __future__ import annotations

from math import comb

from fourth.orbits import series
from sixth.orbits import (
    APART_KINDS,
    MERGED_KINDS,
    NAMED_KINDS,
    _at_least,
    _averaged,
    _exactly,
    _shifted,
    _unchanged,
    _with_diagonal,
    diag_cycles,
    lost_of_kind,
)
from sixth.orbits import count_free as count_free_part
from xry.orbits import class_size, pair_cycles, partitions
from xry.state import Sameness

__all__ = [
    "APART_KINDS",
    "MERGED_KINDS",
    "NAMED_KINDS",
    "count_free",
    "count_named",
    "counts_by_lost",
    "counts_upto",
    "counts_within",
    "layer_counts",
    "lost_of_kind",
    "product_count",
    "two_term_round_count",
]


def _mul(p: list[int], q: list[int], degree: int) -> list[int]:
    """The product of two polynomials, truncated at `degree`."""
    out = [0] * (degree + 1)
    for i, a in enumerate(p[: degree + 1]):
        if a:
            for j, b in enumerate(q[: degree + 1 - i]):
                out[i + j] += a * b
    return out


def _s_factor(parts: tuple[int, ...], degree: int) -> list[int]:
    """The `s` states left unchanged by a rewriting of cycle type `parts`, by total: every cycle free."""
    return _unchanged(parts, degree, False, None, True)


def count_free(n: int, degree: int, one_way: bool = False, cap: int | None = None, off: bool = True) -> list[int]:
    """States with `n` terms up to any rewriting, by total multiplicity of both relations.

    The restrictions (`one_way`, `cap`, `off`) apply to the `r` part; the
    `s` part is free.
    """
    total = [0] * (degree + 1)
    for parts in partitions(n):
        size = class_size(parts)
        poly = _mul(_unchanged(parts, degree, one_way, cap, off), _s_factor(parts, degree), degree)
        for t, c in enumerate(poly):
            total[t] += size * c
    return _averaged(total, n)


def count_named(n: int, degree: int, cap: int | None = None) -> dict[str, list[int]]:
    """States with `n` terms and names, up to rewritings keeping the names, by kind and total.

    The sixth's `count_named` with every inner polynomial multiplied by the
    `s` factor of the rewriting; `cap` bounds the `xrx` multiplicities.
    """
    total = {kind: [0] * (degree + 1) for kind in NAMED_KINDS}
    for parts in partitions(n):
        size = class_size(parts)
        kept = parts.count(1)
        off = pair_cycles(parts, False)
        diag = diag_cycles(parts)
        s_fac = _s_factor(parts, degree)
        if kept >= 1:
            others_diag = dict(diag)
            others_diag[1] -= 1
            rest = _mul(_with_diagonal(series(off, degree), others_diag, cap, degree), s_fac, degree)
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
        others_off = dict(off)
        others_off[1] -= 2
        rest = _mul(_with_diagonal(series(others_off, degree), diag, cap, degree), s_fac, degree)
        ways = size * kept * (kept - 1)
        for kind, between in (("neither", 0), ("arb only", 1), ("bra only", 1), ("arb and bra", 2)):
            for t, c in enumerate(_shifted(rest, between, degree)):
                total[kind][t] += ways * c
    return {kind: _averaged(counts, n) for kind, counts in total.items()}


def counts_by_lost(sameness: Sameness, bra: bool, n: int, degree: int, cap: int | None = None) -> dict[int, list[int]]:
    """Results with `n` terms by destroyed givens, then by total multiplicity `0..degree`."""
    m0 = 2 if bra else 1
    out: dict[int, list[int]] = {}

    def put(value: int, counts: list[int]) -> None:
        acc = out.setdefault(value, [0] * (degree + 1))
        for t, c in enumerate(counts):
            acc[t] += c

    if sameness is Sameness.ANCHORED:
        for kind, counts in count_named(n, degree, cap).items():
            put(lost_of_kind(bra, kind), counts)
        return out
    if n == 1:
        # One term `c` asserting `crc` `t_r` times and `csc` `t − t_r` times: `lost = m0 + 1 − min(t_r, m0)`.
        for t in range(degree + 1):
            for t_r in range(t + 1):
                if cap is None or t_r <= cap:
                    put(m0 + 1 - min(t_r, m0), [1 if i == t else 0 for i in range(degree + 1)])
        return out
    every = count_free(n, degree, cap=cap)
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
    multiplicity at most `k + 3`, as under the sixth seed.
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


def counts_within(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, int]:
    """The independent count by "terms/total/destroyed givens", restricted to cost within `rounds`."""
    size0 = 2 + (2 if bra else 1)
    out: dict[str, int] = {}
    for n in range(1, bound + 1):
        for value, counts in counts_by_lost(sameness, bra, n, size0 + rounds).items():
            for t, c in enumerate(counts):
                if c and n + t - size0 + 2 * value <= rounds:
                    out[f"{n}/{t}/{value}"] = c
    return out


def product_count(n: int, degree: int) -> list[int]:
    """The product of the single-relation counts, by total: what `count_free` would be if the relations were counted apart."""
    single = count_free_part(n, degree)
    return _mul(single, single, degree)


def _c(n: int, k: int) -> int:
    """`C(n, k)`, zero when `n < k` or `n < 0`."""
    return comb(n, k) if 0 <= k <= n else 0


def _two_term_r_kinds(bra: bool, k: int) -> int:
    """The sixth's two-term results of round `k` that have two terms (names apart, or one term with a second)."""
    if not bra:
        return _c(k + 3, 3) + _c(k + 1, 2) + _c(k - 1, 2) + _c(k + 1, 3)
    both_missing = k - 1 if k >= 2 else 0
    return _c(k + 3, 3) + 2 * _c(k + 1, 2) + both_missing + _c(k - 2, 2) + _c(k - 1, 2) + _c(k + 1, 3)


def _one_term_count(bra: bool, r: int) -> int:
    """The one-term results of round `r`: `ara` `K` times and `asa` `L` times with cost(K) + L = r."""
    if not bra:
        # cost(0) = 2, cost(K) = K for K ≥ 1
        return int(r >= 2) + r
    # cost(0) = 3, cost(1) = 2, cost(K) = K − 1 for K ≥ 2
    return int(r >= 3) + int(r >= 2) + r


def two_term_round_count(bra: bool, r: int) -> int:
    """Results of round `r` with at most the given terms, names kept, in closed form.

    The sixth's two-term kinds of round `k` (`_two_term_r_kinds`), each with
    an `s` part of total `r − k` on two terms (`C(r − k + 3, 3)` ways),
    summed over `k`; plus the one-term states.
    """
    if r < 0:
        raise ValueError("a round is not negative")
    return _one_term_count(bra, r) + sum(_two_term_r_kinds(bra, k) * _c(r - k + 3, 3) for k in range(r + 1))
