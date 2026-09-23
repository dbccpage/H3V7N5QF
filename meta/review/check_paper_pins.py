"""Compare existing paper watchlist pins with the pre-review local main.

The review may add watched digests and pins for its fenced prose. It must
preserve the earlier per-paper census exactly. This is a local Git read.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = "53b319a48f347b1a52e823ea7db46c79f8434c42"
WATCHLIST = ROOT / "ci" / "prose_watchlist.json"
OUTPUT = Path(__file__).with_name("paper_pins_check.json")


def paper_path(path: str) -> bool:
    return path == "paper/paper.md" or (path.startswith("paper/") and path.endswith("/paper.md"))


def main() -> int:
    previous = subprocess.run(
        ["git", "show", f"{BASE}:ci/prose_watchlist.json"],
        cwd=ROOT, capture_output=True, check=True,
    )
    old = json.loads(previous.stdout)
    current = json.loads(WATCHLIST.read_text(encoding="utf-8"))
    old_pins = {k: v for k, v in old["baseline"].items() if paper_path(k)}
    new_pins = {k: v for k, v in current["baseline"].items() if paper_path(k)}
    changed = sorted(k for k in old_pins.keys() | new_pins.keys() if old_pins.get(k) != new_pins.get(k))
    result = {
        "base_commit": BASE,
        "paper_files_with_pins_before": len(old_pins),
        "paper_files_with_pins_after": len(new_pins),
        "changed_paper_pins": changed,
        "pass": not changed,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if not changed else 1


if __name__ == "__main__":
    raise SystemExit(main())
