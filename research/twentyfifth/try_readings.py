"""Scratch (not evidence): every reading at a small bound — results, rounds against the cost formula, told.

Run from the repository root: `python research/twentyfifth/try_readings.py BOUND ROUNDS`.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentyfifth.explore import explore  # noqa: E402
from twentyfifth.readings import READINGS, explore_reading, i3_reach_failures  # noqa: E402


def main() -> None:
    bound, rounds = int(sys.argv[1]), int(sys.argv[2])
    chosen = explore(bound, rounds)
    print("main exploration:", len(chosen.round_of), "results")
    for reading in READINGS:
        t0 = time.time()
        run = explore_reading(reading, bound, rounds)
        bad = [m for m, r in run.round_of.items() if run.cost(m) != r]
        told = sum(1 for m in run.round_of if run.told(m))
        extra = ""
        if reading.identify == "keep":
            extra = f", reach failures {i3_reach_failures(run)}"
            if bad:
                m = min(bad, key=lambda k: run.round_of[k])
                extra += f", first cost failure {run.first[m]} round {run.round_of[m]} formula {run.cost(m)}"
        print(f"{reading.name}: {len(run.round_of)} results, per round {run.per_round()}, round != cost {len(bad)}, "
              f"told {told}{extra} ({time.time() - t0:.1f}s)")


if __name__ == "__main__":
    main()
