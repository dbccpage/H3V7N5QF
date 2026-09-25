"""Counting the results of the twenty-third seed without the exploration.

Derived (paper, D11)
    * One term: raising adds nothing (there is no other term), so the results
      are the twenty-second's: one recording no assertion, two for every
      `t ≥ 1` (`one_term_count`).
    * Two terms: a result is its two loops' excesses and the two-way sum
      `e(0, 1) + e(1, 0)` (raising moves the two pair excesses in opposite
      directions), up to exchanging the two terms, which exchanges the loops;
      its fewest assertions is `t = |d0| + |d1| + |S|`.  The points of `Z³`
      with `|d0| + |d1| + |S| = t` number `4t² + 2`, the exchange fixes `2t`
      of them (`d0 = d1`), so `two_term_count(t) = 2t² + t + 1` for `t ≥ 1`,
      one for `t = 0`; the results of round `r` with at most two terms are
      `[r = 0] + [r ≥ 1]·one(r − 1) + [r ≥ 2]·two(r − 2)`
      (`two_term_round_count`): of order `2r²`, where the twenty-second's were
      of order `(4/3)r³`.
    * Three terms: a result is its three loops' excesses, its three two-way
      sums and its sum `T` around `0, 1, 2`, up to the rewritings of the three
      terms (a rewriting that turns the three terms around the other way turns
      `T` into `ΣS − T`), with the closed-form cost of `twentythird.cost`
      (`three_term_counts`: listed from these numbers, not from states).
    * Any number of terms (`listing_counts`): every excess table of weight at
      most `t`, grouped by `result_key`, each result counted at the least
      weight among its tables — which is its fewest, since a state asserting
      the fewest is one of the tables.  Independent of the changes.

Unlike the twenty-second's (`twentysecond.orbits`), these counts are not a
factor per cycle of pairs: the cost of a result is not a sum over pairs.
"""

from __future__ import annotations

from collections.abc import Iterator
from functools import lru_cache
from itertools import permutations

from twentythird.state import Key, plain_of, result_key

__all__ = [
    "counts_within",
    "layer_counts",
    "listing_counts",
    "off_diagonal_tables",
    "one_term_count",
    "tables",
    "three_term_counts",
    "two_term_count",
    "two_term_count_by_points",
    "two_term_round_count",
]


def one_term_count(t: int) -> int:
    """Results with one term recording `t` assertions: the loop's excess is `±t`."""
    if t < 0:
        raise ValueError("a number of assertions is not negative")
    return 1 if t == 0 else 2


def two_term_count(t: int) -> int:
    """Results with two terms recording `t` assertions, in closed form."""
    if t < 0:
        raise ValueError("a number of assertions is not negative")
    return 1 if t == 0 else 2 * t * t + t + 1


def two_term_count_by_points(t: int) -> int:
    """The same count by listing: the points `(d0, d1, S)` of `Z³` at distance `t`, and those the exchange
    fixes (`d0 = d1`), halved."""
    if t < 0:
        raise ValueError("a number of assertions is not negative")
    points = sum(1 for p in _l1_points(3, t) if sum(abs(v) for v in p) == t)
    fixed = sum(1 for d in range(-t, t + 1) for s in range(-t, t + 1) if 2 * abs(d) + abs(s) == t)
    return (points + fixed) // 2


def two_term_round_count(r: int) -> int:
    """Results of round `r` with at most two terms, in closed form."""
    if r < 0:
        raise ValueError("a round is not negative")
    return int(r == 0) + (one_term_count(r - 1) if r >= 1 else 0) + (two_term_count(r - 2) if r >= 2 else 0)


def _l1_points(dim: int, radius: int) -> Iterator[tuple[int, ...]]:
    """Every point of `Z^dim` whose absolute values add up to at most `radius`."""
    if dim == 0:
        yield ()
        return
    for v in range(-radius, radius + 1):
        for rest in _l1_points(dim - 1, radius - abs(v)):
            yield (v, *rest)


def three_term_counts(degree: int) -> list[int]:
    """Results with three terms by recorded assertions `0..degree`, from the loops, two-way sums and `T`."""
    # A result: loops (d0, d1, d2), two-way sums on {0,1}, {1,2}, {2,0}, and T around 0 -> 1 -> 2 -> 0.
    seen: set[tuple[int, ...]] = set()
    counts = [0] * (degree + 1)
    edges = ((0, 1), (1, 2), (2, 0))
    for point in _l1_points(6, degree):
        d = point[:3]
        s = point[3:]
        top = sum(max(v, 0) for v in s)
        bottom = -sum(max(-v, 0) for v in s)
        base = sum(abs(v) for v in point)
        spare = (degree - base) // 2
        for t in range(bottom - spare, top + spare + 1):
            w = base + 2 * max(0, t - top, bottom - t)  # at most `degree`: `t` stays within `spare`
            forms = []
            for p in permutations(range(3)):
                loops = tuple(d[p.index(x)] for x in range(3))
                # the two-way sum on the new pair {p[a], p[b]} is the old one on {a, b}
                new_s = {}
                for (a, b), v in zip(edges, s):
                    new_s[frozenset((p[a], p[b]))] = v
                sums = tuple(new_s[frozenset(e)] for e in edges)
                # the new triple 0 -> 1 -> 2 is the old one around p^-1: forward if p keeps the turn
                turn = [p.index(x) for x in range(3)]
                forward = (turn[1] - turn[0]) % 3 == 1
                new_t = t if forward else sum(s) - t
                forms.append((*loops, *sums, new_t))
            mark = min(forms)
            if mark not in seen:
                seen.add(mark)
                counts[w] += 1
    return counts


def tables(n: int, radius: int) -> Iterator[tuple[int, ...]]:
    """Every excess table on `n` terms of weight at most `radius`."""
    return _l1_points(n * n, radius)


def off_diagonal_tables(n: int, weight: int) -> Iterator[tuple[int, ...]]:
    """Every excess table on `n` terms with nothing on the loops and weight exactly `weight`, in a fixed order."""
    cells = [x * n + y for x in range(n) for y in range(n) if x != y]
    for point in _l1_points(len(cells), weight):
        if sum(abs(v) for v in point) == weight:
            table = [0] * (n * n)
            for i, v in zip(cells, point):
                table[i] = v
            yield tuple(table)


@lru_cache(maxsize=None)
def listing_counts(n: int, degree: int) -> list[int]:
    """Results with `n` terms by recorded assertions `0..degree`, from every excess table of weight ≤ degree."""
    least: dict[Key, int] = {}
    for table in tables(n, degree):
        w = sum(abs(e) for e in table)
        k = result_key(plain_of(n, table))
        if k not in least or w < least[k]:
            least[k] = w
    counts = [0] * (degree + 1)
    for w in least.values():
        counts[w] += 1
    return counts


def _counts(n: int, degree: int) -> list[int]:
    if n == 0:
        return [1] + [0] * degree
    if n == 1:
        return [one_term_count(t) for t in range(degree + 1)]
    if n == 2:
        return [two_term_count(t) for t in range(degree + 1)]
    if n == 3:
        return three_term_counts(degree)
    return listing_counts(n, degree)


def counts_within(bound: int, rounds: int) -> dict[str, int]:
    """The results within `bound` terms and `rounds` rounds, by "terms/assertions" (non-zero counts only)."""
    out: dict[str, int] = {}
    for n in range(min(bound, rounds) + 1):
        for t, c in enumerate(_counts(n, rounds - n)):
            if c:
                out[f"{n}/{t}"] = c
    return out


def layer_counts(upto: int) -> list[int]:
    """How many results need exactly `k` changes, `k = 0..upto`, with no bound on terms."""
    layers = [0] * (upto + 1)
    for n in range(upto + 1):
        for t, c in enumerate(_counts(n, upto - n)):
            layers[n + t] += c
    return layers
