"""Scratch (not evidence): how long the exploration takes at candidate bounds.

Run from the repository root: `python research/twentyfifth/time_explore.py BOUND ROUNDS`.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentyfifth.cost import cost  # noqa: E402
from twentyfifth.explore import explore  # noqa: E402


def main() -> None:
    bound, rounds = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    g = explore(bound, rounds)
    t1 = time.time()
    bad = sum(1 for k, r in g.round_of.items() if cost(g.representative(k)) != r)
    per_round = [sum(1 for r in g.round_of.values() if r == k) for k in range(rounds + 1)]
    print(f"bound {bound} rounds {rounds}: states {len(g.states.depth)}, results {len(g.round_of)}, "
          f"round != cost: {bad}, per round {per_round}, {t1 - t0:.1f}s")


if __name__ == "__main__":
    main()
