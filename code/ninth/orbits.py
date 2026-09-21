"""Counting the results of the ninth seed without listing them.

Computed.  Every well-formed two-relation state is a result, the empty one
included (a theorem of the paper), so the results with `n` terms are all the
two-relation states with `n` terms up to any rewriting, by total multiplicity
of both relations: the eighth derivation's `count_free` (the orbit method
with the rewriting acting on all `n²` ordered pairs twice, every cycle
contributing the series `1 / (1 − x^L)` once for `r` and once for `s`), which
mentions no name and no given and is imported.  With `n = 0` it gives the
empty state alone.  The cost of a result being its size, the number of
results of each round follows (`layer_counts`), and the results within a
bound on terms and rounds are counted by (terms, total) as the completeness
certificate (`counts_within`).

**The count is not a product** (the eighth's D10, surviving verbatim: the
eighth's count under any rewriting *is* this seed's count).  For `n ≥ 2` the
number of results with `n` terms exceeds the product of the seventh's
single-relation counts (`product_count`), since one rewriting must fix both
relations at once; for `n ≤ 1` the two agree.

Derived (paper)
    * With two terms the eight multiplicities (four in `r`, four in `s`)
      summing to `t`, up to the swap of the two terms, number
      `(C(t+7, 7) + [t even]·C(t/2 + 3, 3)) / 2` (`two_term_count`): the
      compositions of `t` into eight parts, plus the ones the swap fixes
      (`ara = brb`, `arb = bra`, and the same in `s`, so `t` even), halved.
      The one-term states of total `t` number `t + 1` (`one_term_count`).  So
      the results of round `r` with at most two terms are
      `[r = 0] + [r ≥ 1]·r + [r ≥ 2]·two_term_count(r − 2)`
      (`two_term_round_count`): 1, 1, 3, 7, 23, 64, 175, 402, 866, …
    * The results whose two relations agree everywhere (`r = s`) with `n`
      terms and total `t` number the seventh's count with `n` terms and
      total `t / 2` for even `t`, none for odd `t` (`agreeing_count`): a
      rewriting fixes `(r, r)` exactly when it fixes `r`.
    * A one-term result asserting `ara` `p` times and `asa` `q` times is
      reached by `C(p + q, p)` shortest sequences (`one_term_sequences`): the
      term, then the `p + q` assertions in any order — where the seventh had
      exactly one.

Cited from the seventh and eighth derivations (`seventh.orbits`,
`eighth.orbits`) and re-checked
    `count_free` and `product_count` (the eighth's) and `count_results` (the
    seventh's single-relation count) mention no name and no given and
    survive; the seventh's `two_term_count`, `two_term_round_count`,
    `layer_counts` and `counts_within` are written again for two relations.
"""

from __future__ import annotations

from math import comb

from eighth.orbits import count_free, product_count
from seventh.orbits import count_results as count_results_part

__all__ = [
    "agreeing_count",
    "agreeing_within",
    "count_results",
    "count_results_part",
    "counts_within",
    "layer_counts",
    "one_term_count",
    "one_term_sequences",
    "product_count",
    "two_term_count",
    "two_term_round_count",
]


def count_results(n: int, degree: int) -> list[int]:
    """Results with `n` terms by total multiplicity `0..degree` (both relations), up to rewriting."""
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


def one_term_count(t: int) -> int:
    """Results with exactly one term and total multiplicity `t`: `ara` `p` times, `asa` `t − p` times."""
    if t < 0:
        raise ValueError("a total multiplicity is not negative")
    return t + 1


def two_term_count(t: int) -> int:
    """Results with exactly two terms and total multiplicity `t` (both relations), in closed form."""
    if t < 0:
        raise ValueError("a total multiplicity is not negative")
    fixed = comb(t // 2 + 3, 3) if t % 2 == 0 else 0
    return (comb(t + 7, 7) + fixed) // 2


def two_term_round_count(r: int) -> int:
    """Results of round `r` with at most two terms, in closed form."""
    if r < 0:
        raise ValueError("a round is not negative")
    return int(r == 0) + (one_term_count(r - 1) if r >= 1 else 0) + (two_term_count(r - 2) if r >= 2 else 0)


def agreeing_count(n: int, t: int) -> int:
    """Results with `n` terms and total `t` whose two relations agree everywhere: the seventh's count at `t / 2`."""
    if n < 0 or t < 0:
        raise ValueError("terms and total multiplicity are not negative")
    if t % 2:
        return 0
    return count_results_part(n, t // 2)[t // 2]


def agreeing_within(bound: int, rounds: int) -> int:
    """How many results within `bound` terms and `rounds` rounds have their two relations agreeing everywhere."""
    return sum(agreeing_count(n, t) for n in range(min(bound, rounds) + 1) for t in range(rounds - n + 1))


def one_term_sequences(p: int, q: int) -> int:
    """Shortest sequences reaching the one-term result asserting `ara` `p` times and `asa` `q` times."""
    if p < 0 or q < 0:
        raise ValueError("a multiplicity is not negative")
    return comb(p + q, p)
