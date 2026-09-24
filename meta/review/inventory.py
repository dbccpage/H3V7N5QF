"""Make a compact reading index for the 21 derivations.

This is an index for human review, not a correctness gate or a replacement for
reading the source, proof, and evidence cited by an individual claim.
"""

from __future__ import annotations

import ast
import difflib
import json
import re
from pathlib import Path

from audit_ledger import ORDINALS, ROOT, local_paths, report_names


PARENT = {
    **{name: prior for prior, name in zip(ORDINALS, ORDINALS[1:10])},
    **{name: "ninth" for name in ORDINALS[10:16]},
    "sixteenth": "fourteenth",
    **{name: "base" for name in ORDINALS[16:]},
}


def location(name: str, kind: str) -> Path:
    if name == "base":
        return ROOT / kind / ("seed_prompt.md" if kind == "prompt" else "paper.md")
    return ROOT / kind / name / ("seed_prompt.md" if kind == "prompt" else "paper.md")


def check_fields(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    return [
        node.target.id
        for class_node in tree.body if isinstance(class_node, ast.ClassDef) and class_node.name.endswith("Check")
        for node in class_node.body if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name)
    ]


def main() -> None:
    rows: list[str] = [
        "# Derivation reading index",
        "",
        "Generated from the current local files. These counts and snippets are navigation",
        "aids, not evidence of a theorem or of a completed audit.",
        "The single-ID count excludes grouped ledger rows such as base `G1–G14`;",
        "`claim_audit.csv` counts those rows separately.",
        "",
    ]
    for name in ORDINALS:
        paper, ledger, summary_path, report = local_paths(name)
        if name == "base":
            evidence_py = ROOT / "code/xry/evidence.py"
            change_log = ROOT / "paper/change_log.md"
        else:
            evidence_py = ROOT / "code" / name / "evidence.py"
            change_log = ROOT / "paper" / name / "change_log.md"
        seed = location(name, "prompt")
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
        paper_text = paper.read_text(encoding="utf-8")
        ledger_text = ledger.read_text(encoding="utf-8")
        rows.extend([
            f"## {name}",
            "",
            f"- Parent: {PARENT.get(name, 'none')}.",
            f"- Source sizes (bytes): seed {seed.stat().st_size}; paper {paper.stat().st_size}; ledger {ledger.stat().st_size}; change log {change_log.stat().st_size}; evidence.py {evidence_py.stat().st_size}.",
            f"- Single-ID ledger rows: {len(re.findall(r'^\| [A-Z][0-9]+ \|', ledger_text, re.M))}; printed axiom names: {len(report_names(report))}.",
            f"- Disagreement fields: {', '.join(check_fields(evidence_py)) or '(none)' }.",
            f"- Summary top keys: {', '.join(summary)}.",
            "- Paper headings: " + " / ".join(
                h.strip("# ") for h in paper_text.splitlines() if h.startswith("## ")
            ),
            "- Open ledger rows:",
        ])
        open_rows = [line for line in ledger_text.splitlines() if line.startswith("| O")]
        rows.extend("  - " + line[:300].rstrip() for line in open_rows)
        if not open_rows:
            rows.append("  - (none)")
        if name in PARENT:
            before = location(PARENT[name], "prompt").read_text(encoding="utf-8").splitlines()
            after = seed.read_text(encoding="utf-8").splitlines()
            diff = list(difflib.unified_diff(before, after, fromfile=PARENT[name], tofile=name, lineterm="", n=0))
            rows.extend(["- Seed diff:", "", "```diff", *diff, "```"])
        rows.append("")
    output = ROOT / "meta/review/reading_index.md"
    while rows and not rows[-1]:
        rows.pop()
    output.write_text("\n".join(rows) + "\n", encoding="utf-8", newline="\n")
    print(output.relative_to(ROOT))


if __name__ == "__main__":
    main()
