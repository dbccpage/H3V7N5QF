"""Counting the results of the sixteenth seed without listing them.

Computed.  Every well-formed state — a ninth state with any record over its
terms — is a result (a theorem of the paper), so the results with `n` terms
are counted by the orbit method with the rewriting acting on all `n²` ordered
pairs *three* times: once for `r`, once for `s`, once for the record.  A
rewriting leaves a state unchanged exactly when each of the three is the same
all along each cycle of pairs; a cycle of length `L` contributes the series
`1 / (1 − x^L)` for `r`, the same for `s`, and `1 / (1 − x^{2L})` for the
record, since a recorded leftover weighs two in the potential (an addition
and a removal).  The results of round `k` with `n` terms are those of weight
`k − n`.  With the record read as a set (the unchosen C-R2) the third factor
is `1 + x^{2L}`; with the record left out it is `1`, which recovers the
ninth's count of the results with an empty record (`ninth_part`).

Derived (paper)
    * The one-term results of round `k ≥ 1` number
      `(⌊(k−1)/2⌋ + 1) · (⌈(k−1)/2⌉ + 1)` (`one_term_round_count`): the
      triples `(α, β, γ)` with `α + β + 2γ = k − 1`.
    * The count is not a product: with two terms the results exceed the
      product of the ninth's count and the one-relation count of the record
      (`product_count16`), one rewriting having to fix all three at once.

Cited from the ninth, eighth, sixth, fourth and first derivations
(`ninth.orbits`, `eighth.orbits`, `sixth.orbits`, `fourth.orbits`,
`xry.orbits`) and re-checked
    `partitions`, `class_size`, `pair_cycles`, `diag_cycles` (the cycles of
    a rewriting on ordered pairs, diagonal included) and `series` mention no
    record and survive; the ninth's `count_results` is the record-free part
    of this count and is compared with it (`ninth_part`).
"""

from __future__ import annotations

from math import factorial

from fourth.orbits import series
from ninth.orbits import count_results as count_results_ninth
from sixth.orbits import diag_cycles
from xry.orbits import class_size, pair_cycles, partitions

from sixteenth.state import Reading

__all__ = [
    "count_results16",
    "counts_within16",
    "layer_counts16",
    "ninth_part",
    "one_term_round_count",
    "product_count16",
    "two_term_round_count16",
]


def _mul(p: list[int], q: list[int], degree: int) -> list[int]:
    """The product of two polynomials, truncated at `degree`."""
    out = [0] * (degree + 1)
    for i, a in enumerate(p[: degree + 1]):
        if a:
            for j, b in enumerate(q[: degree + 1 - i]):
                out[i + j] += a * b
    return out


def _all_pair_cycles(parts: tuple[int, ...]) -> dict[int, int]:
    """Cycle lengths (with multiplicity) of all `n²` ordered pairs under a rewriting of cycle type `parts`."""
    cycles = dict(pair_cycles(parts, False))
    for length, count in diag_cycles(parts).items():
        cycles[length] = cycles.get(length, 0) + count
    return cycles


def _record_factor(poly: list[int], cycles: dict[int, int], degree: int, reading: Reading | None) -> list[int]:
    """`poly` times the record's factor per cycle: `1 / (1 − x^{2L})`, or `1 + x^{2L}` (set), or nothing."""
    if reading is None:
        return poly
    acc = list(poly)
    for length, count in sorted(cycles.items()):
        for _ in range(count):
            step = 2 * length
            if reading is Reading.SET:
                acc = [acc[i] + (acc[i - step] if i >= step else 0) for i in range(degree + 1)]
            else:
                for i in range(step, degree + 1):
                    acc[i] += acc[i - step]
    return acc


def _averaged(total: list[int], n: int) -> list[int]:
    order = factorial(n)
    if any(c % order for c in total):
        raise ArithmeticError("an orbit count is a whole number")
    return [c // order for c in total]


def count_results16(n: int, degree: int, reading: Reading | None = Reading.COUNT) -> list[int]:
    """Results with `n` terms up to any rewriting, by weight `0..degree` (both totals plus twice the record).

    `reading` selects the record's factor: `COUNT` (the chosen reading),
    `SET` (C-R2), or `None` for no record at all (the ninth's count).  The
    unchosen `DROP` reading has the same results as `COUNT`.
    """
    if n < 0 or degree < 0:
        raise ValueError("terms and weight are not negative")
    if reading is Reading.DROP:
        reading = Reading.COUNT
    total = [0] * (degree + 1)
    for parts in partitions(n):
        cycles = _all_pair_cycles(parts)
        one = series(cycles, degree)
        poly = _record_factor(_mul(one, one, degree), cycles, degree, reading)
        size = class_size(parts)
        for w, c in enumerate(poly):
            total[w] += size * c
    return _averaged(total, n)


def ninth_part(n: int, degree: int) -> tuple[list[int], list[int]]:
    """The results with an empty record by both totals, beside the ninth's count: they must agree."""
    return count_results16(n, degree, None), count_results_ninth(n, degree)


def product_count16(n: int, degree: int) -> list[int]:
    """The ninth's count times the record's one-relation count with weight two, by weight.

    What the count would be if the record were counted apart from the two
    relations; it equals `count_results16` for at most one term and falls
    short from two terms on.
    """
    ninth = count_results_ninth(n, degree)
    record = [0] * (degree + 1)
    for parts in partitions(n):
        cycles = _all_pair_cycles(parts)
        poly = _record_factor([1] + [0] * degree, cycles, degree, Reading.COUNT)
        size = class_size(parts)
        for w, c in enumerate(poly):
            record[w] += size * c
    return _mul(ninth, _averaged(record, n), degree)


def layer_counts16(upto: int, reading: Reading | None = Reading.COUNT) -> list[int]:
    """How many results need exactly `k` changes, for `k = 0..upto`, with no bound on terms."""
    layers = [0] * (upto + 1)
    for n in range(upto + 1):
        for w, c in enumerate(count_results16(n, upto - n, reading)):
            layers[n + w] += c
    return layers


def counts_within16(bound: int, rounds: int, reading: Reading | None = Reading.COUNT) -> dict[str, int]:
    """The results within `bound` terms and `rounds` rounds, by "terms/weight" (non-zero counts only)."""
    out: dict[str, int] = {}
    for n in range(min(bound, rounds) + 1):
        for w, c in enumerate(count_results16(n, rounds - n, reading)):
            if c:
                out[f"{n}/{w}"] = c
    return out


def one_term_round_count(k: int) -> int:
    """Results of round `k` with exactly one term, in closed form: `(⌊(k−1)/2⌋ + 1)·(⌈(k−1)/2⌉ + 1)` for `k ≥ 1`."""
    if k < 0:
        raise ValueError("a round is not negative")
    if k == 0:
        return 0
    m = k - 1
    return (m // 2 + 1) * ((m + 1) // 2 + 1)


def two_term_round_count16(k: int) -> int:
    """Results of round `k` with at most two terms, by the series (no closed form is claimed)."""
    if k < 0:
        raise ValueError("a round is not negative")
    return sum(count_results16(n, k - n)[k - n] for n in range(min(2, k) + 1))
