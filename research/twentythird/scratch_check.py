"""Scratch checks of the twenty-third seed's arithmetic (not evidence).

Run from the repository root: `python research/twentythird/scratch_check.py`.
"""

from __future__ import annotations

import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

Table = tuple[int, ...]


def shift(n: int, e: Table, g: tuple[int, ...]) -> Table:
    return tuple(e[x * n + y] + g[x] - g[y] for x in range(n) for y in range(n))


def weight(e: Table) -> int:
    return sum(abs(v) for v in e)


def descent(n: int, e: Table) -> tuple[int, ...]:
    g = [0] * n
    cur = weight(e)
    while True:
        best = None
        for mask in range(1, (1 << n) - 1):
            h = tuple(g[x] + ((mask >> x) & 1) for x in range(n))
            w = weight(shift(n, e, h))
            if w < cur:
                best = (w, h)
                break
        if best is None:
            return tuple(g)
        cur, g = best[0], list(best[1])


def brute(n: int, e: Table, box: int) -> int:
    best = weight(e)
    for rest in itertools.product(range(-box, box + 1), repeat=n - 1):
        g = (0, *rest)
        best = min(best, weight(shift(n, e, g)))
    return best


def three_closed(e: Table) -> int:
    n = 3
    loops = sum(abs(e[x * n + x]) for x in range(3))
    pairs = [(0, 1), (1, 2), (2, 0)]
    s = [e[x * n + y] + e[y * n + x] for x, y in pairs]
    t = sum(e[x * n + y] for x, y in pairs)
    p = sum(max(v, 0) for v in s)
    q = sum(max(-v, 0) for v in s)
    dist = max(0, t - p, -q - t)
    return loops + sum(abs(v) for v in s) + 2 * dist


def main() -> None:
    rng = random.Random(1)
    for n in (2, 3, 4):
        for _ in range(300):
            e = tuple(rng.randint(-3, 3) for _ in range(n * n))
            d = weight(shift(n, e, descent(n, e)))
            m = max(abs(v) for v in e)
            b = brute(n, e, (n - 1) * m + 1)
            assert d == b, (n, e, d, b)
            if n == 3:
                assert d == three_closed(e), (e, d, three_closed(e))
            if n == 2:
                assert d == abs(e[0]) + abs(e[3]) + abs(e[1] + e[2])
    print("descent == search, closed forms agree")
    # four-term witness: no single term (raise x or raise all but x) lowers, but some set does
    n = 4
    off = [(x, y) for x in range(n) for y in range(n) if x != y]
    found = None
    for total in range(1, 6):
        for support in itertools.combinations(range(len(off)), total):
            # multiplicity one on each chosen pair, every sign
            for signs in itertools.product((1, -1), repeat=total):
                e = [0] * 16
                for (i, sg) in zip(support, signs):
                    x, y = off[i]
                    e[x * n + y] = sg
                et = tuple(e)
                w = weight(et)
                single = [1 << x for x in range(n)] + [((1 << n) - 1) ^ (1 << x) for x in range(n)]
                if any(weight(shift(n, et, tuple((m >> x) & 1 for x in range(n)))) < w for m in single):
                    continue
                if weight(shift(n, et, descent(n, et))) < w:
                    found = et
                    break
            if found:
                break
        if found:
            break
    print("smallest four-term witness (multiplicities one):", found, "weight", weight(found) if found else None)
    # two-term counts
    for t in range(0, 8):
        pts = set()
        for d0 in range(-t, t + 1):
            for d1 in range(-t, t + 1):
                for s in range(-t, t + 1):
                    if abs(d0) + abs(d1) + abs(s) == t:
                        pts.add(min((d0, d1, s), (d1, d0, s)))
        want = 1 if t == 0 else 2 * t * t + t + 1
        assert len(pts) == want, (t, len(pts), want)
    print("two-term counts 2t^2+t+1")


if __name__ == "__main__":
    main()
