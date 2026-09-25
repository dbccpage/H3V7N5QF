"""Scratch (not evidence): regenerate `evidence/twentyfifth/` and report how long it took.

Run from the repository root: `python research/twentyfifth/time_run.py [--check]`.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentyfifth.__main__ import main  # noqa: E402

start = time.time()
code = main(sys.argv[1:])
print(f"exit={code} seconds={time.time() - start:.0f}")
