"""Scratch (not evidence): the differential checks at small bounds, and where they disagree."""

from __future__ import annotations

import sys
import time

sys.path.insert(0, "code")

from twentyfourth.evidence import audit  # noqa: E402

t = time.time()
check = audit(2, 4)
for name, items in check.as_dict().items():
    print(name, len(items), items[:3])
print("clean:", check.clean(), f"{time.time() - t:.1f}s")
