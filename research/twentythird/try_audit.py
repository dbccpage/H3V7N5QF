"""Scratch: run the audit and print the non-empty disagreement lists (not evidence)."""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentythird.evidence import audit  # noqa: E402


def main() -> None:
    args = [int(a) for a in sys.argv[1:]] or [2, 4, 4]
    t0 = time.time()
    check = audit(*args)
    print("clean", check.clean(), round(time.time() - t0, 1), "s")
    for name, items in check.as_dict().items():
        if items:
            print(name, len(items), items[:5])


if __name__ == "__main__":
    main()
