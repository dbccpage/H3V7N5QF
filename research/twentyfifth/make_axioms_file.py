"""Write `lean4_core/Twentyfifth/Axioms.lean`: `#print axioms` for every theorem of the library, and for every
theorem of `Twentythird` or `Twentysecond` the paper or ledger cites (imported, used as they stand).

Research helper (not evidence): run it after adding theorems or citations, then
`python code/lean_report_twentyfifth.py`.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
ROOT = REPO / "lean4_core"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z0-9_.']+)", re.MULTILINE)
NAMESPACE = re.compile(r"^(namespace|end)\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)
ORDER = ("Fill", "Balance", "Blind", "Cost", "Record", "Map", "Reach", "Rename")
BACKTICK = re.compile(r"`([A-Za-z_][\w'.]*)`")


def declared(text: str) -> list[str]:
    """Fully qualified theorem names, following `namespace` / `end` blocks."""
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


own: list[str] = []
lines = [
    "import Twentyfifth",
    "",
    "/-! `#print axioms` for every theorem of the library, file by file, then for every theorem of `Twentythird`",
    "or `Twentysecond` the paper or ledger cites (imported).  Only `propext` and `Quot.sound` are allowed",
    "(`code/twentyfifth/leanreport.py`). -/",
    "",
]
for name in ORDER:
    path = ROOT / "Twentyfifth" / f"{name}.lean"
    if not path.is_file():
        continue
    names = declared(path.read_text(encoding="utf-8"))
    own.extend(names)
    lines.append(f"-- Twentyfifth/{name}.lean")
    lines.extend(f"#print axioms {decl}" for decl in names)

earlier: dict[str, str] = {}
for lib in ("Twentythird", "Twentysecond"):
    for path in sorted((ROOT / lib).glob("*.lean")):
        if path.name == "Axioms.lean":
            continue
        for full in declared(path.read_text(encoding="utf-8")):
            earlier.setdefault(full.split(".", 1)[1], full)  # the name as written after `theorem`
own_short = {n.split(".", 1)[1] for n in own}
cited: list[str] = []
for doc in ("paper.md", "claim_ledger.md"):
    text = (REPO / "paper" / "twentyfifth" / doc).read_text(encoding="utf-8")
    for token in BACKTICK.findall(text):
        if token in earlier and token not in own_short and earlier[token] not in cited:
            cited.append(earlier[token])
lines.append("-- imported from Twentythird and Twentysecond, cited by the paper or the ledger")
lines.extend(f"#print axioms {full}" for full in sorted(cited))
(ROOT / "Twentyfifth" / "Axioms.lean").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
print(len(own), "theorems of the library,", len(cited), "imported theorems cited")
