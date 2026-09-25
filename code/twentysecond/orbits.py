"""Counting the results of the twenty-second seed without listing them.

Computed.  A result with `n` terms is an excess function on the `n²` ordered
pairs (a whole number at each, of either sign) up to rewriting the terms
(paper; `lean4_core/Twentysecond/Same.lean`, `Rename.lean`); its cost is
`n + Σ |excess|`.  Orbit counting: average, over the rewritings of `n`
terms, the excess functions a rewriting leaves unchanged — those constant
on every cycle of ordered pairs.  A cycle of length `L` carrying the value
`e` weighs `L·|e|`, so each cycle contributes `1 + 2(x^L + x^{2L} + …) =
(1 + x^L)/(1 − x^L)` (`count_results`).  This is independent of the
exploration (`twentysecond.explore`); agreement between the two is the
completeness certificate within the bound.

Derived (paper)
    * With one term: the one excess `e(0, 0)` is any whole number; total
      `t = |e|`: one result for `t = 0`, two for every `t ≥ 1`
      (`one_term_count`).
    * With two terms: the four excesses with `Σ |e| = t` number
      `8t(t² + 2)/3` for `t ≥ 1` (by how many are non-zero:
      `Σ_k C(4, k)·2^k·C(t − 1, k − 1)`), and the swap of the two terms fixes
      `2t` of them for even `t ≥ 2` (`e00 = e11`, `e01 = e10`); halved:
      `4t(t² + 2)/3 + [t even]·t` for `t ≥ 1`, `1` for `t = 0`
      (`two_term_count`).  So the results of round `r` with at most two
      terms are `[r = 0] + [r ≥ 1]·one(r − 1) + [r ≥ 2]·two(r − 2)`
      (`two_term_round_count`): 1, 1, 3, 6, 20, 46, 102, 182, 312, … — of
      order `r³`, where the ninth's were of order `r⁷`.

Cited from the first derivation (`xry.orbits`) and re-checked (no change)
    `partitions` (cycle types of the rewritings of `n` terms) and
    `class_size` (how many rewritings have a cycle type) mention no state.
"""

from __future__ import annotations

from math import comb, factorial, gcd

from xry.orbits import class_size, partitions

__all__ = [
    "all_pair_cycles",
    "count_results",
    "counts_within",
    "layer_counts",
    "one_term_count",
    "two_term_count",
    "two_term_count_by_parts",
    "two_term_round_count",
]


def all_pair_cycles(parts: tuple[int, ...]) -> dict[int, int]:
    """Cycle lengths (with multiplicity) of all `n²` ordered pairs under a rewriting of cycle type `parts`."""
    out: dict[int, int] = {}
    for i, p in enumerate(parts):
        out[p] = out.get(p, 0) + p
        for q in parts[i + 1 :]:
            g = gcd(p, q)
            lcm = p * q // g
            out[lcm] = out.get(lcm, 0) + 2 * g
    return out


def _cycle_factor(poly: list[int], length: int, degree: int) -> list[int]:
    """`poly` times `(1 + x^L)/(1 − x^L) = 1 + 2 Σ_{k ≥ 1} x^{kL}`, truncated at `degree`."""
    out = list(poly)
    for i, c in enumerate(poly):
        if c:
            for j in range(i + length, degree + 1, length):
                out[j] += 2 * c
    return out


def count_results(n: int, degree: int) -> list[int]:
    """Results with `n` terms by recorded assertions `t = Σ |excess|`, `t = 0..degree`."""
    if n < 0 or degree < 0:
        raise ValueError("terms and assertions are not negative")
    total = [0] * (degree + 1)
    for parts in partitions(n):
        poly = [1] + [0] * degree
        for length, count in sorted(all_pair_cycles(parts).items()):
            for _ in range(count):
                poly = _cycle_factor(poly, length, degree)
        size = class_size(parts)
        for t, c in enumerate(poly):
            total[t] += size * c
    order = factorial(n)
    if any(c % order for c in total):
        raise ArithmeticError("an orbit count is a whole number")
    return [c // order for c in total]


def layer_counts(upto: int) -> list[int]:
    """How many results need exactly `k` changes, for `k = 0..upto`, with no bound on terms."""
    layers = [0] * (upto + 1)
    for n in range(upto + 1):
        for t, c in enumerate(count_results(n, upto - n)):
            layers[n + t] += c
    return layers


def counts_within(bound: int, rounds: int) -> dict[str, int]:
    """The results within `bound` terms and `rounds` rounds, by "terms/assertions" (non-zero counts only)."""
    out: dict[str, int] = {}
    for n in range(min(bound, rounds) + 1):
        for t, c in enumerate(count_results(n, rounds - n)):
            if c:
                out[f"{n}/{t}"] = c
    return out


def one_term_count(t: int) -> int:
    """Results with one term recording `t` assertions: `e(0, 0) = ±t`."""
    if t < 0:
        raise ValueError("a number of assertions is not negative")
    return 1 if t == 0 else 2


def two_term_count(t: int) -> int:
    """Results with two terms recording `t` assertions, in closed form."""
    if t < 0:
        raise ValueError("a number of assertions is not negative")
    if t == 0:
        return 1
    return 4 * t * (t * t + 2) // 3 + (t if t % 2 == 0 else 0)


def two_term_count_by_parts(t: int) -> int:
    """The same count by how many of the four excesses are non-zero (the step of the proof)."""
    if t < 0:
        raise ValueError("a number of assertions is not negative")
    if t == 0:
        return 1
    points = sum(comb(4, k) * (1 << k) * comb(t - 1, k - 1) for k in range(1, 5))
    fixed = 0 if t % 2 else sum(comb(2, k) * (1 << k) * comb(t // 2 - 1, k - 1) for k in range(1, 3))
    return (points + fixed) // 2


def two_term_round_count(r: int) -> int:
    """Results of round `r` with at most two terms, in closed form."""
    if r < 0:
        raise ValueError("a round is not negative")
    return int(r == 0) + (one_term_count(r - 1) if r >= 1 else 0) + (two_term_count(r - 2) if r >= 2 else 0)
