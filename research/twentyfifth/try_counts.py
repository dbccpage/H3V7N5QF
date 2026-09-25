"""Scratch (not evidence): the independent count against the exploration, and timings.

Run from the repository root: `python research/twentyfifth/try_counts.py BOUND ROUNDS`.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentyfifth.explore import explore  # noqa: E402
from twentyfifth.orbits import counts_within  # noqa: E402


def main() -> None:
    bound, rounds = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    g = explore(bound, rounds)
    t1 = time.time()
    got: dict[str, int] = {}
    for mark, r in g.round_of.items():
        n, _, filled = mark
        label = f"{n}/{r - n - len(filled)}/{len(filled)}"
        got[label] = got.get(label, 0) + 1
    want = counts_within(bound, rounds)
    t2 = time.time()
    bad = sorted(k for k in set(got) | set(want) if got.get(k, 0) != want.get(k, 0))
    print(f"explore {t1 - t0:.1f}s, count {t2 - t1:.1f}s, results {sum(got.values())} vs {sum(want.values())}, "
          f"labels differing: {bad[:10]}")


if __name__ == "__main__":
    main()
