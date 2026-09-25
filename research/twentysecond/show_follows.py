"""Summarise the statements tested in `evidence/twentysecond/follows_*.csv` (research helper, not evidence)."""

from __future__ import annotations

import csv
from pathlib import Path

for path in sorted((Path(__file__).resolve().parents[2] / "evidence" / "twentysecond").glob("follows_*.csv")):
    with path.open(encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    independent = [r["statement"] for r in rows if r["first_holds"] and r["first_fails"]]
    never = [r["statement"] for r in rows if not r["first_holds"]]
    always = [r["statement"] for r in rows if not r["first_fails"]]
    print(path.name, len(rows), "independent", len(independent), "never", never, "always", always)
