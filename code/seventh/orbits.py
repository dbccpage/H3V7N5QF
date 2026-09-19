"""Counting the results of the seventh seed without listing them.

Computed.  Every well-formed counted state is a result, the empty one
included (a theorem of the paper), so the results with `n` terms are all the
counted states with `n` terms up to any rewriting, by total multiplicity:
the sixth derivation's `count_free` (the orbit method with the rewriting
acting on all `n²` ordered pairs, each cycle contributing the series
`1 / (1 − x^L)`), which mentions no name and no given and is imported.  With
`n = 0` it gives the empty state alone.  The cost of a result being its
size, the number of results of each round follows (`layer_counts`), and the
results within a bound on terms and rounds are counted by (terms, total) as
the completeness certificate (`counts_within`).

Derived (paper)
    With two terms the four multiplicities `(p, i, j, q)` of `ara`, `arb`,
    `bra`, `brb` summing to `t`, up to the swap `(p, i, j, q) ↔ (q, j, i, p)`,
    number `(C(t+3, 3) + [t even](t/2 + 1)) / 2` (`two_term_count`): the
    compositions of `t` into four parts, plus the ones the swap fixes
    (`p = q`, `i = j`, so `t` even), halved.  So the results of round `r` with
    at most two terms are `[r = 0] + [r ≥ 1] + [r ≥ 2]·two_term_count(r − 2)`
    (`two_term_round_count`): 1, 1, 2, 3, 7, 11, 20, 29, 45, 61, 86, …

Cited from the first derivation (`xry.orbits`) and re-checked
    `partitions`, `class_size`, `pair_cycles` mention no assertion and
    survive; they are used through `sixth.orbits.count_free`.
"""

from __future__ import annotations

from math import comb

from sixth.orbits import count_free

__all__ = ["count_results", "counts_within", "layer_counts", "two_term_count", "two_term_round_count"]


def count_results(n: int, degree: int) -> list[int]:
    """Results with `n` terms by total multiplicity `0..degree`, up to rewriting."""
    if n < 0 or degree < 0:
        raise ValueError("terms and total multiplicity are not negative")
    return count_free(n, degree)


def layer_counts(upto: int) -> list[int]:
    """How many results need exactly `k` changes, for `k = 0..upto`, with no bound on terms.

    A result of round `k` has size `k`: at most `k` terms and total
    multiplicity at most `k`.
    """
    layers = [0] * (upto + 1)
    for n in range(upto + 1):
        counts = count_results(n, upto - n)
        for t, c in enumerate(counts):
            layers[n + t] += c
    return layers


def counts_within(bound: int, rounds: int) -> dict[str, int]:
    """The results within `bound` terms and `rounds` rounds, by "terms/total" (non-zero counts only)."""
    out: dict[str, int] = {}
    for n in range(min(bound, rounds) + 1):
        for t, c in enumerate(count_results(n, rounds - n)):
            if c:
                out[f"{n}/{t}"] = c
    return out


def two_term_count(t: int) -> int:
    """Results with exactly two terms and total multiplicity `t`, in closed form."""
    if t < 0:
        raise ValueError("a total multiplicity is not negative")
    fixed = t // 2 + 1 if t % 2 == 0 else 0
    return (comb(t + 3, 3) + fixed) // 2


def two_term_round_count(r: int) -> int:
    """Results of round `r` with at most two terms, in closed form."""
    if r < 0:
        raise ValueError("a round is not negative")
    return int(r == 0) + int(r >= 1) + (two_term_count(r - 2) if r >= 2 else 0)
