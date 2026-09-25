"""Write `lean4_core/Twentyfourth/Axioms.lean`: `#print axioms` for every theorem of the library.

Research helper (not evidence): run it after adding theorems, then
`python code/lean_report_twentyfourth.py`.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2] / "lean4_core"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z0-9_.']+)", re.MULTILINE)
ORDER = ("Basic", "Same", "Tell", "Record", "Cost", "Reach", "Swap", "Map", "Rename")

lines = [
    "import Twentyfourth",
    "",
    "/-! `#print axioms` for every theorem of the library, file by file.  Only `propext` and",
    "`Quot.sound` are allowed (`code/twentyfourth/leanreport.py`). -/",
    "",
]
#: Earlier theorems the paper and ledger name (imported; Lean re-checks them when this library is built).
CITED = (
    "Twentysecond.reach_plainSt",
    "Twentysecond.Step.phi_le",
    "Twentysecond.Step.phi_identify",
    "Twentysecond.Reach.n_pos",
    "Twentysecond.excess_swap",
    "Twentysecond.swap_swap",
    "Twentythird.gen3_iff_same3",
    "Twentythird.Same3.loop",
    "Twentythird.Same3.size_parity",
    "Twentythird.same3_nothing_iff",
    "Twentythird.arcThree_not_nothing",
    "Twentythird.addTerm_not_respected",
    "Twentythird.cost3_iff",
    "Twentythird.phi_ge_around",
    "Twentythird.excess_rename",
    "Twentythird.seventh_pair_merge",
)

for name in ORDER:
    text = (ROOT / "Twentyfourth" / f"{name}.lean").read_text(encoding="utf-8")
    lines.append(f"-- Twentyfourth/{name}.lean")
    lines.extend(f"#print axioms Twentyfourth.{decl}" for decl in DECL.findall(text))
lines.append("-- earlier theorems the paper names (imported)")
lines.extend(f"#print axioms {decl}" for decl in CITED)
(ROOT / "Twentyfourth" / "Axioms.lean").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
print(sum(1 for line in lines if line.startswith("#print")), "theorems")
