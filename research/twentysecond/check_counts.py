"""Scratch check of the orbit counts against a brute-force listing (research, not evidence)."""

from __future__ import annotations

import sys
from itertools import permutations, product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentysecond.orbits import (  # noqa: E402
    count_results,
    layer_counts,
    two_term_count,
    two_term_count_by_parts,
    two_term_round_count,
)


def brute(n: int, t: int) -> int:
    seen = set()
    for e in product(range(-t, t + 1), repeat=n * n):
        if sum(abs(v) for v in e) != t:
            continue
        seen.add(min(tuple(e[p[x] * n + p[y]] for x in range(n) for y in range(n)) for p in permutations(range(n))))
    return len(seen)


print([two_term_round_count(r) for r in range(10)])
print([two_term_count(t) for t in range(8)], [two_term_count_by_parts(t) for t in range(8)])
print(count_results(2, 7), [brute(2, t) for t in range(6)])
print(count_results(1, 5), count_results(0, 3))
print(count_results(3, 3), [brute(3, t) for t in range(4)])
print(layer_counts(8))
