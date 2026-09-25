"""Counting the results of the twenty-fifth seed without the exploration.

Derived (paper, D9)
    A result is a twenty-third result together with a set of filled triples,
    up to one rewriting of both.  Fix a twenty-third result `R` on `n` terms and
    the rewritings that keep it (its stabilizer, found on one of its excess
    tables); the results over `R` with `f` filled triples are the orbits of
    the `f`-sets of triples under that stabilizer, counted by averaging over
    it the sets each rewriting keeps — a set kept by a rewriting is a union of
    its cycles on the triples, so each cycle of length `L` contributes a factor
    `1 + x^L` (`fill_orbits`).  The cost of such a result is `n + w + f`, `w`
    the fewest assertions of `R`.

Cited from the twenty-third derivation (`twentythird.orbits`, `twentythird.state`)
and re-checked (computed again)
    The twenty-third results with `n` terms and fewest `w` are listed from every
    excess table of weight at most `w`, grouped by the twenty-third's mark
    (`classes`): its own listing, independent of the changes.  With at most two
    terms nothing can be filled and the twenty-third's closed form applies
    (`two_term_round_count`).
"""

from __future__ import annotations

from functools import lru_cache

from fourth.state import _rewritings
from twentythird.orbits import tables, two_term_round_count
from twentythird.state import Key, Table, normal_table, plain_of, result_key, rewrite_table

from twentyfifth.state import oriented_triples, way_round

__all__ = ["classes", "counts_within", "fill_orbits", "stabilizer", "two_term_round_count"]


@lru_cache(maxsize=None)
def classes(n: int, weight: int) -> tuple[tuple[Key, int, Table], ...]:
    """The twenty-third results with `n` terms and fewest at most `weight`: mark, fewest, a table of that weight."""
    best: dict[Key, tuple[int, Table]] = {}
    for table in tables(n, weight):
        w = sum(abs(e) for e in table)
        k = result_key(plain_of(n, table))
        if k not in best or w < best[k][0]:
            best[k] = (w, table)
    return tuple(sorted((k, w, t) for k, (w, t) in best.items()))


def stabilizer(n: int, table: Table) -> list[tuple[int, ...]]:
    """The rewritings of the terms that keep the twenty-third result of `table`."""
    want = normal_table(n, table)
    return [p for p, _ in _rewritings(n) if normal_table(n, rewrite_table(n, table, p)) == want]


def fill_orbits(n: int, group: list[tuple[int, ...]], most: int) -> list[int]:
    """Orbits of the sets of `f` filled triples, `f = 0 … most`, under the rewritings `group`."""
    triples = oriented_triples(n)
    total = [0] * (most + 1)
    for p in group:
        seen: set[tuple[int, int, int]] = set()
        poly = [1] + [0] * most
        for t in triples:
            if t in seen:
                continue
            length = 0
            cur = t
            while cur not in seen:
                seen.add(cur)
                length += 1
                cur = way_round(p[cur[0]], p[cur[1]], p[cur[2]])
            nxt = poly[:]
            for i in range(most + 1 - length):
                nxt[i + length] += poly[i]
            poly = nxt
        total = [a + b for a, b in zip(total, poly)]
    size = len(group)
    if any(v % size for v in total):
        raise ArithmeticError("a count of orbits is a whole number")
    return [v // size for v in total]


def counts_within(bound: int, rounds: int) -> dict[str, int]:
    """The results within `bound` terms and `rounds` rounds, by "terms/assertions/filled" (non-zero only)."""
    out: dict[str, int] = {}
    for n in range(min(bound, rounds) + 1):
        spare = rounds - n
        for _, w, table in classes(n, spare):
            fills = fill_orbits(n, stabilizer(n, table), spare - w)
            for f, c in enumerate(fills):
                if c:
                    label = f"{n}/{w}/{f}"
                    out[label] = out.get(label, 0) + c
    return out
