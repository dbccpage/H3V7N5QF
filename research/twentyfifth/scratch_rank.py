"""Scratch (not evidence): ranks of the sums around filled triples, blind results, deciding sets.

Run from the repository root: `python research/twentyfifth/scratch_rank.py`.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations


def rank(rows: list[list[int]]) -> int:
    m = [[Fraction(v) for v in r] for r in rows]
    rk = 0
    cols = len(m[0]) if m else 0
    for c in range(cols):
        piv = next((i for i in range(rk, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][c] != 0:
                f = m[i][c] / m[rk][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
    return rk


def around_row(n: int, x: int, y: int, z: int) -> list[int]:
    row = [0] * (n * n)
    for a, b in ((x, y), (y, z), (z, x)):
        row[a * n + b] += 1
    return row


def oriented(n: int) -> list[tuple[int, int, int]]:
    out = []
    for x, y, z in combinations(range(n), 3):
        out.append((x, y, z))
        out.append((x, z, y))
    return out


def coboundary_rows(n: int) -> list[list[int]]:
    rows = []
    for t in range(1, n):
        row = [0] * (n * n)
        for y in range(n):
            if y != t:
                row[t * n + y] += 1
                row[y * n + t] -= 1
        rows.append(row)
    return rows


def main() -> None:
    for n in range(3, 7):
        rows = [around_row(n, *f) for f in oriented(n)]
        r = rank(rows)
        # blind space modulo coboundaries: n^2 - r - (n - 1); loops are n of it
        blind = n * n - r - (n - 1)
        print(f"n={n}: oriented triples {len(rows)}, rank {r}, blind dims {blind}, beyond loops {blind - n}")
    # antisymmetric part: rank needed C(n-1, 2); with 4 terms, which unordered sets decide
    for n in (3, 4, 5):
        triples = list(combinations(range(n), 3))
        need = (n - 1) * (n - 2) // 2
        # restrict to antisymmetric excess: coordinates e(x,y) for x<y, e(y,x) = -e(x,y)
        pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]

        def arow(t: tuple[int, int, int]) -> list[int]:
            x, y, z = t
            row = [0] * len(pairs)
            for a, b in ((x, y), (y, z), (z, x)):
                if a < b:
                    row[pairs.index((a, b))] += 1
                else:
                    row[pairs.index((b, a))] -= 1
            return row

        full = rank([arow(t) for t in triples])
        print(f"n={n}: antisymmetric sums around, rank of all {full}, needed {need}")
        by_size: dict[int, list[int]] = {}
        for k in range(len(triples) + 1):
            decide = 0
            total = 0
            for sub in combinations(triples, k):
                total += 1
                if sub and rank([arow(t) for t in sub]) == need:
                    decide += 1
                elif not sub and need == 0:
                    decide += 1
            by_size[k] = [decide, total]
            if n == 5 and k > 7:
                break
        print(f"   deciding sets by size (deciding, all): {by_size}")
    # three-term blind with a two-way sum: e(a,b)=1, e(a,c)=1, e(c,b)=-1, e(c,a)=-1
    n = 3
    e = [0] * 9
    e[0 * 3 + 1] = 1
    e[0 * 3 + 2] = 1
    e[2 * 3 + 1] = -1
    e[2 * 3 + 0] = -1
    for f in oriented(3):
        print("around", f, sum(a * b for a, b in zip(around_row(3, *f), e)))
    # four terms: describe the blind family beyond loops by a basis
    n = 4
    rows = [around_row(n, *f) for f in oriented(n)] + coboundary_rows(n)
    for x in range(n):
        row = [0] * 16
        row[x * n + x] = 1
        rows.append(row)
    print("n=4 rank with coboundaries and loops:", rank(rows), "of 16")
    _ = permutations


if __name__ == "__main__":
    main()
