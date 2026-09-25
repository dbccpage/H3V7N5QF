"""Scratch (not evidence): the prose watchlist's hits in one file, with line numbers and the final section's start.

Run from the repository root: `python research/twentyfifth/watch_file.py paper/twentyfifth/paper.md`.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "ci"))

import check_prose_watchlist as w  # noqa: E402

data = w.load(ROOT / w.WATCHLIST_REL)
watched = data["watched"] if "watched" in data else data["terms"]  # type: ignore[index]
path = ROOT / sys.argv[1]
text = path.read_text(encoding="utf-8")
final = next((i for i, line in enumerate(text.splitlines(), start=1) if line.startswith("## 11.")), None)
hits = w.scan_text(text, watched)  # type: ignore[arg-type]
print("final section starts at line", final)
counts: dict[str, int] = {}
for hit in hits:
    print(hit.line, hit.surface, hit.digest[:12], "FINAL" if final and hit.line >= final else "BODY")
    counts[hit.digest] = counts.get(hit.digest, 0) + 1
print(counts)
