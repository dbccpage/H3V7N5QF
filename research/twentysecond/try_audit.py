"""Scratch: run the audit at small bounds and print every non-empty disagreement (research, not evidence)."""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentysecond.evidence import audit  # noqa: E402

t0 = time.perf_counter()
check = audit(2, 4, 4, 1, 2)
print(f"{time.perf_counter() - t0:.1f}s")
for name, values in check.as_dict().items():
    if values:
        print(name, len(values), values[:5])
print("clean", check.clean())
t0 = time.perf_counter()
check = audit(3, 5, 5, 2, 3)
print(f"{time.perf_counter() - t0:.1f}s")
for name, values in check.as_dict().items():
    if values:
        print(name, len(values), values[:5])
print("clean", check.clean())
