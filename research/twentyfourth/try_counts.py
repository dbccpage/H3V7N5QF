"""Scratch (not evidence): the independent counts against the explorations, and the two-term closed form."""

from __future__ import annotations

import sys
import time

sys.path.insert(0, "code")

from twentyfourth.explore import explore  # noqa: E402
from twentyfourth.orbits import counts_within, two_term_count, two_term_count_by_points, two_term_round_count  # noqa: E402

for k in (0, 1, 2):
    for t in range(8):
        assert two_term_count(k, t) == two_term_count_by_points(k, t), (k, t)
print("two-term closed form = listing for t < 8")

for bound, rounds in [(2, 12), (3, 8), (4, 7), (5, 8)]:
    t0 = time.time()
    g = explore(bound, rounds)
    explored: dict[str, int] = {}
    for key, r in g.round_of.items():
        m = g.representative(key)
        label = f"{m.n}/{m.filled_count}/{r - m.n - m.filled_count}"
        explored[label] = explored.get(label, 0) + 1
    counted = counts_within(bound, rounds)
    diff = {k: (explored.get(k, 0), counted.get(k, 0)) for k in set(explored) | set(counted) if explored.get(k, 0) != counted.get(k, 0)}
    per_round = [0] * (rounds + 1)
    for key, r in g.round_of.items():
        per_round[r] += key[0] <= 2
    closed = [two_term_round_count(r) for r in range(rounds + 1)]
    print(bound, rounds, len(g.round_of), "diff:", diff, "two-term ok:", per_round == closed if bound >= 2 else None, f"{time.time() - t0:.1f}s")
