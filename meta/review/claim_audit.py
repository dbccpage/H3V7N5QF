"""Make a per-row evidence index for review; textual links are not proof.

This intentionally records every ledger row so manual review can find an
unsupported statement. It checks syntax, path resolution, and whether a
derived/computed/refuted row supplies an evidence cell. It cannot decide
whether a cited theorem has the stated conclusion.
"""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NAMES = (
    "base", "second", "third", "fourth", "fifth", "sixth", "seventh",
    "eighth", "ninth", "tenth", "eleventh", "twelfth", "thirteenth",
    "fourteenth", "fifteenth", "sixteenth", "seventeenth", "eighteenth",
    "nineteenth", "twentieth", "twentyfirst",
)
CLAIM = re.compile(r"^[A-Z][A-Z0-9]*(?:[–-][A-Z0-9]+)?$")
CODE = re.compile(r"`([^`]+)`")
PATH_END = (".json", ".jsonl", ".csv", ".txt", ".lean", ".py", ".md")
SUPPORT_STATUSES = ("derived", "computed", "refuted")


def ledger(name: str) -> Path:
    return ROOT / "paper" / ("" if name == "base" else name) / "claim_ledger.md"


def split_row(line: str) -> list[str]:
    cells: list[str] = []
    current: list[str] = []
    in_code = False
    escaped = False
    for char in line.strip()[1:-1]:
        if char == "`" and not escaped:
            in_code = not in_code
        if char == "|" and not in_code and not escaped:
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(char)
        escaped = (char == "\\" and not escaped)
    cells.append("".join(current).strip())
    return cells


def resolve_path(token: str, name: str) -> bool:
    if token.startswith("python "):
        token = token.split()[1]
    if "*" in token or not token.endswith(PATH_END):
        return True
    if token in {"paper.md", "change_log.md", "claim_ledger.md"}:
        return (ROOT / "paper" / ("" if name == "base" else name) / token).is_file()
    if token.endswith(".lean") and "/" not in token:
        return any((ROOT / "lean4").glob("**/" + token))
    if token.endswith(".py") and "/" not in token:
        return any((ROOT / "code").glob("**/" + token))
    if "/" in token:
        return (ROOT / token).is_file()
    return (ROOT / "evidence" / ("" if name == "base" else name) / token).is_file()


def rows(name: str) -> list[dict[str, str]]:
    path = ledger(name)
    out: list[dict[str, str]] = []
    columns: list[str] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.startswith("|"):
            continue
        cells = split_row(line)
        if cells and cells[0].strip().lower() == "id":
            columns = [c.lower() for c in cells]
            continue
        if not cells or not CLAIM.fullmatch(cells[0]):
            continue
        if not columns or len(cells) != len(columns):
            raise ValueError(f"{path}:{line_no}: {len(cells)} cells for {len(columns)} columns")
        item = dict(zip(columns, cells, strict=True))
        evidence = item.get("evidence", "")
        status = item.get("status", "").lower()
        missing = sorted({token for token in CODE.findall(evidence) if not resolve_path(token, name)})
        out.append({
            "derivation": name,
            "line": str(line_no),
            "id": cells[0],
            "status": status,
            "statement": item.get("statement", ""),
            "evidence": evidence,
            "recheck": item.get("re-check", item.get("re-check ", "")),
            "missing_paths": ", ".join(missing),
            "missing_evidence": str(status.startswith(SUPPORT_STATUSES) and evidence in {"", "—", "none"}),
        })
    return out


def main() -> None:
    all_rows = [item for name in NAMES for item in rows(name)]
    out = ROOT / "meta" / "review" / "claim_audit.csv"
    with out.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(all_rows[0]))
        writer.writeheader()
        writer.writerows(all_rows)
    summary = {
        "rows": len(all_rows),
        "per_derivation": {name: sum(r["derivation"] == name for r in all_rows) for name in NAMES},
        "missing_evidence": [f"{r['derivation']}:{r['id']}" for r in all_rows if r["missing_evidence"] == "True"],
        "missing_paths": [f"{r['derivation']}:{r['id']}:{r['missing_paths']}" for r in all_rows if r["missing_paths"]],
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
