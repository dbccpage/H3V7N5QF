"""Scratch (not evidence): which statements hold in every explored result, and which depend on the state."""

from __future__ import annotations

import csv
from pathlib import Path

for tag in ("bound5_rounds7", "bound3_rounds9", "bound2_rounds16"):
    rows = list(csv.DictReader(Path(f"evidence/twentyfourth/follows_{tag}.csv").open(encoding="utf-8")))
    every = [r["statement"] for r in rows if r["in_every_result"] == "1"]
    depends = [(r["statement"], r["results_where_it_depends"]) for r in rows if r["depends_at"]]
    print(tag, len(rows), "statements; in every result:", every)
    print("   depend on the state:", len(depends), depends[:6])
    here = [r for r in rows if r["statement"] in ("some_term_filled", "every_filled_term_balances", "told_apart",
                                                   "unbalanced_loops_filled", "every_term_filled")]
    for r in here:
        print("   ", r["statement"], "holds_at", r["holds_at"], "fails_at", r["fails_at"], "depends", r["depends_at"])
