"""Scratch (not evidence): run the small audit and print every non-empty disagreement list.

Run from the repository root: `python research/twentyfifth/try_audit.py BOUND ROUNDS`.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentyfifth.evidence import audit  # noqa: E402


def main() -> None:
    bound, rounds = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    check = audit(bound, rounds)
    print(f"{time.time() - t0:.1f}s, clean: {check.clean()}")
    for name, items in check.as_dict().items():
        if items:
            print(name, len(items), items[:5])


if __name__ == "__main__":
    main()
