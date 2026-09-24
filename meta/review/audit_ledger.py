"""List citation candidates for human review; this is not a proof gate.

Text matching only identifies omissions to inspect. A reported Lean name must
be resolved with Lean before it becomes a finding.
"""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ORDINALS = (
    "base", "second", "third", "fourth", "fifth", "sixth", "seventh",
    "eighth", "ninth", "tenth", "eleventh", "twelfth", "thirteenth",
    "fourteenth", "fifteenth", "sixteenth", "seventeenth", "eighteenth",
    "nineteenth", "twentieth", "twentyfirst",
)
DECL = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z][A-Za-z0-9_.']*)")
CODE = re.compile(r"`([^`]+)`")
REPORT = re.compile(r"^'([^']+)' (?:depends on axioms:|does not depend)")


def local_paths(name: str) -> tuple[Path, Path, Path, Path]:
    if name == "base":
        return (
            ROOT / "paper" / "paper.md",
            ROOT / "paper" / "claim_ledger.md",
            ROOT / "evidence" / "summary.json",
            ROOT / "evidence" / "lean_axioms.txt",
        )
    return (
        ROOT / "paper" / name / "paper.md",
        ROOT / "paper" / name / "claim_ledger.md",
        ROOT / "evidence" / name / "summary.json",
        ROOT / "evidence" / name / "lean_axioms.txt",
    )


def theorem_names() -> set[str]:
    names: set[str] = set()
    for path in (ROOT / "lean4").glob("**/*.lean"):
        if ".lake" not in path.parts:
            names.update(DECL.findall(path.read_text(encoding="utf-8")))
    return names


def cited_names(text: str, known: set[str]) -> set[str]:
    return {
        token for token in CODE.findall(text)
        if token in known and not token.endswith((".lean", ".json", ".csv", ".txt"))
    }


def file_candidates(text: str, evidence_root: Path) -> list[str]:
    missing: set[str] = set()
    for token in CODE.findall(text):
        short = token.split("::", 1)[0]
        if "*" in short or not short.endswith((".json", ".jsonl", ".csv", ".txt", ".lean", ".py")):
            continue
        path = ROOT / short if "/" in short else evidence_root / short
        if not path.is_file():
            missing.add(short)
    return sorted(missing)


def report_names(path: Path) -> set[str]:
    return {
        match.group(1)
        for line in path.read_text(encoding="utf-8").splitlines()
        if (match := REPORT.match(line)) is not None
    }


def main() -> None:
    known = theorem_names()
    rows: list[dict[str, object]] = []
    for name in ORDINALS:
        paper, ledger, summary, report = local_paths(name)
        assert paper.is_file() and ledger.is_file() and summary.is_file() and report.is_file()
        paper_text = paper.read_text(encoding="utf-8")
        ledger_text = ledger.read_text(encoding="utf-8")
        citations = cited_names(paper_text + "\n" + ledger_text, known)
        printed = report_names(report)
        missing_report = sorted(
            cited for cited in citations
            if not any(full == cited or full.endswith("." + cited) for full in printed)
        )
        evidence_root = summary.parent
        missing_files = file_candidates(paper_text + "\n" + ledger_text, evidence_root)
        rows.append({
            "derivation": name,
            "cited_theorem_candidates": len(citations),
            "axiom_report_names": len(printed),
            "cited_theorems_not_in_own_report_candidates": missing_report,
            "missing_backticked_file_candidates": missing_files,
        })
    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()
