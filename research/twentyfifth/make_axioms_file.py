"""Write `lean4_core/Twentyfifth/Axioms.lean`: `#print axioms` for every theorem of the library.

Research helper (not evidence): run it after adding theorems, then check with
`lake env lean Twentyfifth/Axioms.lean` inside `lean4_core/`, or
`python code/lean_report_twentyfifth.py`.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2] / "lean4_core"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z0-9_.']+)", re.MULTILINE)
NAMESPACE = re.compile(r"^(namespace|end)\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)
ORDER = ("Fill", "Balance", "Blind", "Cost", "Record", "Map", "Reach", "Rename")


def declared(text: str) -> list[str]:
    """Fully qualified theorem names, following `namespace` / `end` blocks inside `Twentyfifth`."""
    out: list[str] = []
    stack: list[str] = []
    events = sorted(
        [(m.start(), "decl", m.group(1)) for m in DECL.finditer(text)]
        + [(m.start(), m.group(1), m.group(2)) for m in NAMESPACE.finditer(text)]
    )
    for _, kind, name in events:
        if kind == "namespace":
            stack.append(name)
        elif kind == "end":
            if stack and stack[-1] == name:
                stack.pop()
        else:
            out.append(".".join([*stack, name]))
    return out


lines = [
    "import Twentyfifth",
    "",
    "/-! `#print axioms` for every theorem of the library, file by file.  Only `propext` and",
    "`Quot.sound` are allowed (`code/twentyfifth/leanreport.py`). -/",
    "",
]
for name in ORDER:
    path = ROOT / "Twentyfifth" / f"{name}.lean"
    if not path.is_file():
        continue
    lines.append(f"-- Twentyfifth/{name}.lean")
    lines.extend(f"#print axioms {decl}" for decl in declared(path.read_text(encoding="utf-8")))
(ROOT / "Twentyfifth" / "Axioms.lean").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
print(sum(1 for line in lines if line.startswith("#print")), "theorems")
