"""Scratch timing of the explorations, to choose the declared bounds (research, not evidence)."""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from ninth.explore import explore as explore_ninth  # noqa: E402
from ninth.state import empty  # noqa: E402
from twentysecond.explore import explore  # noqa: E402

for bound, rounds in ((5, 8), (3, 10), (2, 24), (4, 9), (3, 12), (2, 30)):
    t0 = time.perf_counter()
    e = explore(empty(), bound, rounds)
    print(f"here  {bound} {rounds}: {len(e.depth)} results, {e.attempts_per_round[-1]} attempts, {time.perf_counter() - t0:.1f}s", flush=True)

for bound, rounds in ((5, 8), (3, 9), (2, 12)):
    t0 = time.perf_counter()
    e9 = explore_ninth(empty(), bound, rounds)
    print(f"ninth {bound} {rounds}: {len(e9.depth)} results, {time.perf_counter() - t0:.1f}s", flush=True)
