"""Counting legal states up to sameness without listing them.

Computed.  The method (orbit counting: average, over all rewritings of `n`
terms, the number of legal states a rewriting leaves unchanged) is independent
of the exploration in `xry.explore`; agreement between the two is the
completeness certificate for the exploration within its bound.

A rewriting with cycle lengths `parts` permutes the ordered pairs of distinct
terms; a legal state is left unchanged exactly when its asserted pairs are a
union of cycles of that permutation.  So the states left unchanged, counted
by number of assertions, are the coefficients of a product of `(1 + t**L)`
over the pair cycles, `L` being the cycle length.
"""

from __future__ import annotations

from collections.abc import Iterator
from math import comb, factorial, gcd

from xry.state import Sameness

#: How the two named terms can stand to each other.
NAMED_KINDS = ("a and b one term", "neither", "arb only", "bra only", "arb and bra")


def partitions(n: int) -> Iterator[tuple[int, ...]]:
    """Cycle-length lists of rewritings of `n` terms (non-increasing)."""

    def rec(remaining: int, largest: int) -> Iterator[tuple[int, ...]]:
        if remaining == 0:
            yield ()
            return
        for part in range(min(remaining, largest), 0, -1):
            for rest in rec(remaining - part, part):
                yield (part, *rest)

    return rec(n, n)


def class_size(parts: tuple[int, ...]) -> int:
    """How many rewritings have exactly these cycle lengths."""
    size = factorial(sum(parts))
    for length in set(parts):
        count = parts.count(length)
        size //= length**count * factorial(count)
    return size


def pair_cycles(parts: tuple[int, ...], one_way: bool) -> dict[int, int]:
    """Cycle lengths (with multiplicity) of the pairs under a rewriting.

    `one_way=False`: cycles of ordered pairs of distinct terms.
    `one_way=True`: cycles of unordered pairs that can carry an assertion one
    way only and stay unchanged (a pair turned around by the rewriting
    cannot, and is left out).
    """
    out: dict[int, int] = {}
    for i, p in enumerate(parts):
        inside = (p - 1) // 2 if one_way else p - 1
        if inside:
            out[p] = out.get(p, 0) + inside
        for q in parts[i + 1 :]:
            g = gcd(p, q)
            lcm = p * q // g
            out[lcm] = out.get(lcm, 0) + (g if one_way else 2 * g)
    return out


def expand(cycles: dict[int, int], weight: int, degree: int) -> list[int]:
    """Coefficients up to `degree` of the product of `(1 + weight * t**L)**e`."""
    poly = [1] + [0] * degree
    for length, exponent in sorted(cycles.items()):
        terms = [
            (length * k, comb(exponent, k) * weight**k)
            for k in range(min(exponent, degree // length) + 1)
        ]
        nxt = [0] * (degree + 1)
        for shift, coeff in terms:
            for i in range(degree + 1 - shift):
                nxt[i + shift] += coeff * poly[i]
        poly = nxt
    return poly


def _averaged(total: list[int], n: int) -> list[int]:
    order = factorial(n)
    if any(c % order for c in total):
        raise ArithmeticError("an orbit count is a whole number")
    return [c // order for c in total]


def _degree(n: int, degree: int | None) -> int:
    full = n * (n - 1)
    return full if degree is None else min(full, degree)


def count_free(n: int, degree: int | None = None) -> list[int]:
    """Legal states with `n` terms up to FREE sameness, by assertions `m`."""
    d = _degree(n, degree)
    total = [0] * (d + 1)
    for parts in partitions(n):
        size = class_size(parts)
        for m, c in enumerate(expand(pair_cycles(parts, False), 1, d)):
            total[m] += size * c
    return _averaged(total, n)


def count_one_way(n: int, degree: int | None = None) -> list[int]:
    """As `count_free`, keeping only states with no `xry` and `yrx` together."""
    d = _degree(n, degree)
    total = [0] * (d + 1)
    for parts in partitions(n):
        size = class_size(parts)
        for m, c in enumerate(expand(pair_cycles(parts, True), 2, d)):
            total[m] += size * c
    return _averaged(total, n)


def count_named(n: int, degree: int | None = None) -> dict[str, list[int]]:
    """Legal states with `n` terms and names, up to ANCHORED sameness.

    Split by how `a` and `b` stand to each other (`NAMED_KINDS`), then by
    number of assertions.  A rewriting keeps the names only if it keeps the
    named terms; the pairs `ab`, `ba` are then cycles of length one.
    """
    d = _degree(n, degree)
    total = {kind: [0] * (d + 1) for kind in NAMED_KINDS}
    for parts in partitions(n):
        size = class_size(parts)
        kept = parts.count(1)
        cycles = pair_cycles(parts, False)
        for m, c in enumerate(expand(cycles, 1, d)):
            total["a and b one term"][m] += size * kept * c
        if kept < 2:
            continue
        others = dict(cycles)
        others[1] -= 2
        rest = expand(others, 1, d)
        ways = size * kept * (kept - 1)
        for kind, between in (("neither", 0), ("arb only", 1), ("bra only", 1), ("arb and bra", 2)):
            for m, c in enumerate(rest[: d + 1 - between]):
                total[kind][m + between] += ways * c
    return {kind: _averaged(counts, n) for kind, counts in total.items()}


def count_states(sameness: Sameness, n: int) -> list[int]:
    """All legal states with `n` terms up to `sameness`, by assertions."""
    if sameness is Sameness.FREE:
        return count_free(n)
    named = count_named(n)
    return [sum(col) for col in zip(*named.values())]


#: Destroyed givens by how the named terms stand, without and with `bra` given.
_LOST = {
    False: {"a and b one term": 2, "neither": 1, "arb only": 0, "bra only": 1, "arb and bra": 0},
    True: {"a and b one term": 3, "neither": 2, "arb only": 1, "bra only": 1, "arb and bra": 0},
}


def layer_counts(sameness: Sameness, bra: bool, upto: int) -> list[int]:
    """How many results need exactly `k` changes, for `k = 0..upto`.

    Uses the closed form of `xry.cost` (a theorem), not an exploration, so it
    is exact with no bound on the number of terms: a result needing `k`
    changes has at most `k + 2` terms and at most `k + 4` assertions.
    """
    m0 = 2 if bra else 1
    size0 = 2 + m0
    layers = [0] * (upto + 1)

    def put(n: int, m: int, lost: int, count: int) -> None:
        k = n + m - size0 + 2 * lost
        if 0 <= k <= upto:
            layers[k] += count

    for n in range(1, upto + 3):
        degree = upto + 4
        if sameness is Sameness.ANCHORED:
            for kind, counts in count_named(n, degree).items():
                for m, count in enumerate(counts):
                    put(n, m, _LOST[bra][kind], count)
            continue
        every = count_free(n, degree)
        one_way = count_one_way(n, degree)
        for m, count in enumerate(every):
            if n == 1:
                put(n, m, 1 + m0, count)
            elif m == 0:
                put(n, m, m0, count)
            elif bra:
                put(n, m, 1, one_way[m])
                put(n, m, 0, count - one_way[m])
            else:
                put(n, m, 0, count)
    return layers
