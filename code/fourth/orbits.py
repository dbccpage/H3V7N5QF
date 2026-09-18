"""Counting the results of the fourth seed without listing them.

Computed.  The results with `n` terms and total multiplicity `t` are the
legal counted states with `n` terms, multiplicities adding up to `t`, that
contain what is given (a theorem of the paper), up to sameness.  They are
counted by the orbit method: average, over all rewritings of `n` terms, the
number of such states a rewriting leaves unchanged.  A rewriting leaves a
counted state unchanged exactly when the multiplicity is the same all along
each cycle of the rewriting's action on ordered pairs of distinct terms; so
the unchanged states, counted by total multiplicity, are the coefficients of
a product of series `1 / (1 - x**L)` over the pair cycles, `L` being the cycle
length — where the earlier derivations had the polynomial `(1 + t**L)`.

Cited from the first derivation (`xry.orbits`) and re-checked
    `partitions`, `class_size` and `pair_cycles` describe the rewritings and
    their cycles on pairs; they mention no assertion and survive the
    counting.  The names are handled as in `count_named`: a rewriting keeps
    the names only if it fixes the two named terms, and the pairs `ab`, `ba`
    are then cycles of length one.

Cited from the second and third derivations (`second.orbits`) and re-checked
    `count_results` there counts the results asserting nothing twice; it is
    imported as `count_simple` and its numbers must agree with the sum, over
    all multiplicity patterns with every multiplicity at most one, of the
    counts here (`tests/test_fourth_orbits.py` and `counts.csv`).

Derived (paper)
    The number of results at round `r` is the number of results of size
    `size(given) + r`, so `layer_counts` is exact with no bound on the terms:
    a result of round `r` has at most `r + 2` terms.
"""

from __future__ import annotations

from math import factorial

from second.orbits import count_results as count_simple_by_assertions
from xry.orbits import class_size, pair_cycles, partitions
from xry.state import Sameness

__all__ = ["count_results", "count_simple", "counts_upto", "layer_counts", "series"]


def series(cycles: dict[int, int], degree: int, both_ways_excluded: bool = False) -> list[int]:
    """Coefficients up to `degree` of the product over cycles of `1 / (1 - x**L)`.

    With `both_ways_excluded`, each cycle is a cycle of unordered pairs that
    can carry one direction and stay unchanged, and the factor is
    `(1 + x**L) / (1 - x**L)`: the pair is asserted in neither direction, or
    in exactly one (any positive multiplicity, either direction).
    """
    poly = [1] + [0] * degree
    for length, exponent in sorted(cycles.items()):
        for _ in range(exponent):
            # Multiply by 1 / (1 - x**L): a running sum with step L.
            for i in range(length, degree + 1):
                poly[i] += poly[i - length]
            if both_ways_excluded:
                # Multiply by 1 + x**L.
                for i in range(degree, length - 1, -1):
                    poly[i] += poly[i - length]
    return poly


def _averaged(total: list[int], n: int) -> list[int]:
    order = factorial(n)
    if any(c % order for c in total):
        raise ArithmeticError("an orbit count is a whole number")
    return [c // order for c in total]


def _anchored(bra: bool, n: int, degree: int) -> list[int]:
    """Results with names, `n` terms, by total multiplicity up to `degree`."""
    total = [0] * (degree + 1)
    if n < 2:
        return total
    for parts in partitions(n):
        kept = parts.count(1)
        if kept < 2:
            continue
        cycles = dict(pair_cycles(parts, False))
        cycles[1] -= 2  # the pairs ab and ba are handled apart
        rest = series(cycles, degree)
        ways = class_size(parts) * kept * (kept - 1)
        # ab has multiplicity at least one; ba at least one if given, else any.
        shift = 2 if bra else 1
        # Multiply by x**shift / (1 - x)**2 (the two named pairs): a prefix sum, twice, shifted.
        acc = list(rest)
        for _ in range(2):
            for i in range(1, degree + 1):
                acc[i] += acc[i - 1]
        for t in range(shift, degree + 1):
            total[t] += ways * acc[t - shift]
    return _averaged(total, n)


def _free(bra: bool, n: int, degree: int) -> list[int]:
    """Results without names, `n` terms, by total multiplicity up to `degree`."""
    total = [0] * (degree + 1)
    if n < 1:
        return total
    for parts in partitions(n):
        size = class_size(parts)
        every = series(pair_cycles(parts, False), degree)
        if bra:
            one_way = series(pair_cycles(parts, True), degree, both_ways_excluded=True)
            for t in range(degree + 1):
                total[t] += size * (every[t] - one_way[t])
        else:
            for t in range(1, degree + 1):
                total[t] += size * every[t]
    return _averaged(total, n)


def counts_upto(sameness: Sameness, bra: bool, n: int, degree: int) -> list[int]:
    """Results with `n` terms by total multiplicity `0..degree`."""
    if sameness is Sameness.ANCHORED:
        return _anchored(bra, n, degree)
    return _free(bra, n, degree)


def count_results(sameness: Sameness, bra: bool, n: int, total: int) -> int:
    """Results with `n` terms and total multiplicity `total`."""
    return counts_upto(sameness, bra, n, total)[total]


def count_simple(sameness: Sameness, bra: bool, n: int, degree: int) -> list[int]:
    """Results with `n` terms asserting nothing twice, by number of assertions `0..degree`.

    The earlier derivations' count (`second.orbits.count_results`), padded or
    cut to `degree`.
    """
    counts = count_simple_by_assertions(sameness, bra, n)
    return (counts + [0] * (degree + 1))[: degree + 1]


def layer_counts(sameness: Sameness, bra: bool, upto: int) -> list[int]:
    """How many results need exactly `k` changes, for `k = 0..upto`, with no bound.

    A result needing `k` changes has size `size(given) + k`, so at most
    `k + 2` terms and total multiplicity at most `k + 2`.
    """
    size0 = 2 + (2 if bra else 1)
    layers = [0] * (upto + 1)
    for n in range(2, upto + 3):
        for t, count in enumerate(counts_upto(sameness, bra, n, upto + 2)):
            k = n + t - size0
            if 0 <= k <= upto:
                layers[k] += count
    return layers
