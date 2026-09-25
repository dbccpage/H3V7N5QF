"""Write `lean4_core/Twentythird/Axioms.lean`: `#print axioms` for every theorem of the library.

Research helper (not evidence): run it after adding theorems, then
`python code/lean_report_twentythird.py`.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2] / "lean4_core"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z0-9_.']+)", re.MULTILINE)
ORDER = ("Raise", "Same", "Nothing", "Cost", "Fewest", "Map", "Reach", "Rename")

lines = [
    "import Twentythird",
    "",
    "/-! `#print axioms` for every theorem of the library, file by file.  Only `propext` and",
    "`Quot.sound` are allowed (`code/twentythird/leanreport.py`). -/",
    "",
]
for name in ORDER:
    text = (ROOT / "Twentythird" / f"{name}.lean").read_text(encoding="utf-8")
    lines.append(f"-- Twentythird/{name}.lean")
    lines.extend(f"#print axioms Twentythird.{decl}" for decl in DECL.findall(text))
(ROOT / "Twentythird" / "Axioms.lean").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
print(sum(1 for line in lines if line.startswith("#print")), "theorems")
