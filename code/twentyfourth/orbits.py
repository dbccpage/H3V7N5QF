"""Counting the results of the twenty-fourth seed without the exploration.

A result is a result of the twenty-third (its terms and excess up to raising
and rewriting) together with the set of its filled terms, the same rewriting
acting on both; its cost is `n + k + t`, `k` filled terms and `t` the fewest
assertions (D5).  Counted by `n/k/t`:

Derived (paper, D14)
    * No term: one result.
    * One term: the loop's excess `d` and whether the term is filled; `t = |d|`:
      one result for `t = 0`, two for `t ≥ 1`, for `k = 0` and for `k = 1`.
    * Two terms: the two loops' excesses `d0`, `d1`, the two-way sum `S`, and
      the filled terms `f0`, `f1`, up to exchanging the two terms (which
      exchanges `d0, d1` and `f0, f1`); `t = |d0| + |d1| + |S|`.  The points of
      `Z³` at distance `t ≥ 1` number `4t² + 2`; with no term or both terms
      filled the exchange fixes the `2t` points with `d0 = d1`, so
      `2t² + t + 1`; with one term filled it fixes nothing (it moves the filled
      term), so `4t² + 2`; one result each for `t = 0` (`two_term_count`).
    * Three terms: the three loops, the three two-way sums, the sum `T` around
      `0, 1, 2` and the filled terms, up to the rewritings of the three terms,
      with the twenty-third's closed-form cost (`three_term_counts`).
    * Four or more terms (`listing_counts`): every excess table of weight at
      most `t` with every set of filled terms, grouped by `result_key`, each
      result at the least weight among its tables.

Cited from the twenty-third derivation (`twentythird.orbits`) and re-checked
(re-proved)
    `_l1_points` and `tables` list points of `Z^d`; the three-term count is its
    `three_term_counts` with the filled terms added to what the rewritings
    move.  Its one- and two-term counts are the `k = 0` rows here.
"""

from __future__ import annotations

from functools import lru_cache
from itertools import permutations, product

from twentythird.orbits import _l1_points, tables
from twentythird.state import plain_of

from twentyfourth.state import FState, Key24, result_key

__all__ = [
    "counts_within",
    "layer_counts",
    "listing_counts",
    "one_term_count",
    "one_term_sequences",
    "three_term_counts",
    "two_term_count",
    "two_term_count_by_points",
    "two_term_round_count",
]


def one_term_count(k: int, t: int) -> int:
    """One-term results with `k` filled terms recording `t` assertions."""
    if t < 0 or k not in (0, 1):
        raise ValueError("t is not negative and one term is filled or not")
    return 1 if t == 0 else 2


def one_term_sequences(k: int, t: int) -> int:
    """Shortest sequences to a one-term result: the term, then `t` loops, the filling anywhere after the term."""
    if t < 0 or k not in (0, 1):
        raise ValueError("t is not negative and one term is filled or not")
    return t + 1 if k else 1


def two_term_count(k: int, t: int) -> int:
    """Two-term results with `k` filled terms recording `t` assertions, in closed form."""
    if t < 0 or k not in (0, 1, 2):
        raise ValueError("t is not negative and at most two terms are filled")
    if t == 0:
        return 1
    return 4 * t * t + 2 if k == 1 else 2 * t * t + t + 1


def two_term_count_by_points(k: int, t: int) -> int:
    """The same by listing the points `(d0, d1, S, f0, f1)` and grouping them under the exchange of the terms."""
    seen: set[tuple[int, ...]] = set()
    for d0, d1, s in _l1_points(3, t):
        if abs(d0) + abs(d1) + abs(s) != t:
            continue
        for f0, f1 in product((0, 1), repeat=2):
            if f0 + f1 == k:
                seen.add(min((d0, d1, s, f0, f1), (d1, d0, s, f1, f0)))
    return len(seen)


def two_term_round_count(r: int) -> int:
    """Results of round `r` with at most two terms, in closed form."""
    if r < 0:
        raise ValueError("a round is not negative")
    total = int(r == 0)
    for k in (0, 1):
        t = r - 1 - k
        if t >= 0:
            total += one_term_count(k, t)
    for k in (0, 1, 2):
        t = r - 2 - k
        if t >= 0:
            total += two_term_count(k, t)
    return total


def three_term_counts(degree: int) -> dict[tuple[int, int], int]:
    """Results with three terms by (filled terms, recorded assertions), `k + t ≤ degree`."""
    seen: set[tuple[int, ...]] = set()
    counts: dict[tuple[int, int], int] = {}
    edges = ((0, 1), (1, 2), (2, 0))
    perms = list(permutations(range(3)))
    for point in _l1_points(6, degree):
        d = point[:3]
        s = point[3:]
        top = sum(max(v, 0) for v in s)
        bottom = -sum(max(-v, 0) for v in s)
        base = sum(abs(v) for v in point)
        spare = (degree - base) // 2
        for t in range(bottom - spare, top + spare + 1):
            w = base + 2 * max(0, t - top, bottom - t)
            for f in product((0, 1), repeat=3):
                k = sum(f)
                if w + k > degree:
                    continue
                forms = []
                for p in perms:
                    loops = tuple(d[p.index(x)] for x in range(3))
                    fills = tuple(f[p.index(x)] for x in range(3))
                    new_s = {frozenset((p[a], p[b])): v for (a, b), v in zip(edges, s)}
                    sums = tuple(new_s[frozenset(e)] for e in edges)
                    turn = [p.index(x) for x in range(3)]
                    forward = (turn[1] - turn[0]) % 3 == 1
                    new_t = t if forward else sum(s) - t
                    forms.append((*loops, *sums, new_t, *fills))
                mark = min(forms)
                if mark not in seen:
                    seen.add(mark)
                    counts[(k, w)] = counts.get((k, w), 0) + 1
    return counts


@lru_cache(maxsize=None)
def listing_counts(n: int, degree: int) -> tuple[tuple[tuple[int, int], int], ...]:
    """Results with `n` terms by (filled terms, recorded assertions), `k + t ≤ degree`, by listing."""
    least: dict[Key24, tuple[int, int]] = {}
    for table in tables(n, degree):
        w = sum(abs(e) for e in table)
        base = plain_of(n, table)
        for fills in product((0, 1), repeat=n):
            k = sum(fills)
            if w + k > degree:
                continue
            key = result_key(FState(base, fills))
            if key not in least or w < least[key][1]:
                least[key] = (k, w)
    counts: dict[tuple[int, int], int] = {}
    for kw in least.values():
        counts[kw] = counts.get(kw, 0) + 1
    return tuple(sorted(counts.items()))


def _counts(n: int, degree: int) -> dict[tuple[int, int], int]:
    if n == 0:
        return {(0, 0): 1}
    if n == 1:
        return {(k, t): one_term_count(k, t) for k in (0, 1) for t in range(degree - k + 1)}
    if n == 2:
        return {(k, t): two_term_count(k, t) for k in (0, 1, 2) for t in range(degree - k + 1)}
    if n == 3:
        return three_term_counts(degree)
    return dict(listing_counts(n, degree))


def counts_within(bound: int, rounds: int) -> dict[str, int]:
    """The results within `bound` terms and `rounds` rounds, by "terms/filled/assertions" (every count listed
    is at least one)."""
    out: dict[str, int] = {}
    for n in range(min(bound, rounds) + 1):
        for (k, t), c in sorted(_counts(n, rounds - n).items()):
            out[f"{n}/{k}/{t}"] = c
    return out


def layer_counts(upto: int) -> list[int]:
    """How many results need exactly `c` changes, `c = 0..upto`, with no bound on terms."""
    layers = [0] * (upto + 1)
    for n in range(upto + 1):
        for (k, t), c in _counts(n, upto - n).items():
            layers[n + k + t] += c
    return layers
