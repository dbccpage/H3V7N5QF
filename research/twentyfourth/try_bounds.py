"""Scratch (not evidence): how long the exploration takes at candidate bounds."""

from __future__ import annotations

import sys
import time

sys.path.insert(0, "code")

from twentyfourth.cost import cost  # noqa: E402
from twentyfourth.explore import explore  # noqa: E402

for bound, rounds in [(2, 8), (3, 6), (2, 12), (3, 8), (4, 6), (2, 16), (5, 6), (3, 9), (4, 7), (5, 7)]:
    t = time.time()
    g = explore(bound, rounds)
    bad = sum(1 for k in g.round_of if cost(g.representative(k)) != g.round_of[k])
    print(bound, rounds, len(g.states.depth), len(g.round_of), f"{time.time() - t:.1f}s", "round!=cost:", bad, flush=True)
