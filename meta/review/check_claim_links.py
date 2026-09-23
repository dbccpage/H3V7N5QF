"""Find unresolved ledger evidence links and summary keys for human review.

This does not decide whether a value supports the associated claim.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from audit_ledger import ORDINALS, ROOT, local_paths


TOKEN = re.compile(r"`([^`]+)`")
SUMMARY_KEYS = re.compile(r"`summary\.json`\s*\(([^)]*)\)")
EXT = (".json", ".jsonl", ".csv", ".txt", ".py", ".lean", ".md")


def all_keys(obj: object) -> set[str]:
    if isinstance(obj, dict):
        return set(obj) | set().union(*(all_keys(v) for v in obj.values()))
    if isinstance(obj, list):
        return set().union(*(all_keys(v) for v in obj))
    return set()


def exists(token: str, evidence_dir: Path) -> bool:
    if any(ch in token for ch in ("*", " ", "\n", "…", ":")):
        return True
    paper_dir = ROOT / "paper" / ("" if evidence_dir == ROOT / "evidence" else evidence_dir.name)
    candidates = [ROOT / token, evidence_dir / token, paper_dir / token]
    if token.endswith(".lean"):
        candidates.append(ROOT / "lean4" / token)
        candidates.extend((ROOT / "lean4").glob("*/" + token))
    if token.endswith(".py"):
        candidates.append(ROOT / "code" / token)
        candidates.extend((ROOT / "code").glob("*/" + token))
    return any(path.is_file() for path in candidates)


def main() -> None:
    rows: list[dict[str, object]] = []
    for name in ORDINALS:
        _, ledger, summary_path, _ = local_paths(name)
        evidence_dir = summary_path.parent
        keys = all_keys(json.loads(summary_path.read_text(encoding="utf-8")))
        for line_no, line in enumerate(ledger.read_text(encoding="utf-8").splitlines(), 1):
            if not line.startswith("| "):
                continue
            missing_files = sorted({t for t in TOKEN.findall(line) if t.endswith(EXT) and not exists(t, evidence_dir)})
            missing_keys: list[str] = []
            for match in SUMMARY_KEYS.finditer(line):
                for token in TOKEN.findall(match.group(1)):
                    if "_" in token and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", token) and token not in keys:
                        missing_keys.append(token)
            if missing_files or missing_keys:
                rows.append({"derivation": name, "ledger_line": line_no,
                             "missing_file_candidates": missing_files,
                             "missing_summary_key_candidates": sorted(set(missing_keys))})
    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()
