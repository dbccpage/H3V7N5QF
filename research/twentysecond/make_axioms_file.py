"""Write `lean4_core/Twentysecond/Axioms.lean`: `#print axioms` for every theorem of the library.

Research helper (not evidence): run it after adding theorems, then
`python code/lean_report_twentysecond.py`.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2] / "lean4_core"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z0-9_.']+)", re.MULTILINE)
ORDER = ("Basic", "State", "Plain", "Same", "Cost", "Undo", "Record", "Seventh", "Merge", "Reach", "Swap", "Rename")

lines = [
    "import Twentysecond",
    "",
    "/-! `#print axioms` for every theorem of the library, file by file.  Only `propext` and",
    "`Quot.sound` are allowed (`code/twentysecond/leanreport.py`). -/",
    "",
]
for name in ORDER:
    text = (ROOT / "Twentysecond" / f"{name}.lean").read_text(encoding="utf-8")
    lines.append(f"-- Twentysecond/{name}.lean")
    lines.extend(f"#print axioms Twentysecond.{decl}" for decl in DECL.findall(text))
(ROOT / "Twentysecond" / "Axioms.lean").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
print(sum(1 for line in lines if line.startswith("#print")), "theorems")
