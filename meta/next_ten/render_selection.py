"""Render the declared candidate scores and sensitivity for human review."""

from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main() -> None:
    candidates: list[dict[str, object]] = json.loads((HERE / "candidates.json").read_text(encoding="utf-8"))
    ranking: dict[str, object] = json.loads((HERE / "ranking.json").read_text(encoding="utf-8"))
    by_id = {str(item["id"]): item for item in candidates}
    selected: list[str] = ranking["top_ten"]  # type: ignore[assignment]
    lines = [
        "# Candidate selection (outside the derivational seal)", "",
        "**Status: chosen measure.** The hypothesis in each row is open; the score is a selection device, not a theorem. Weights were fixed in `rubric.md` before any proposal seed was written. `candidates.json`, `rank.py`, and `prototype_results.json` make the choice reproducible.",
        "", "## Selected ten", "",
        "| Rank | Candidate and package | Parent | Score | Hypothesis tested |",
        "|---:|---|---|---:|---|",
    ]
    scores = {str(row["id"]): float(row["score"]) for row in ranking["all_scores"]}  # type: ignore[index]
    for rank, ident in enumerate(selected, 1):
        item = by_id[ident]
        package = f"{rank:02d}-{item['slug']}"
        lines.append(f"| {rank} | {ident} [`{package}`]({package}/why.md) | {item['parent']} | {scores[ident]:g} | {item['hypothesis']} |")
    lines += [
        "", "C11 and C17 tie at 78; both are kept. C06 is scored in the full list but excluded after its prototype exposed an unresolved obstruction-answer rule. C08 is retained as a scored candidate but demoted by its bounded result-set comparison. These decisions precede the ten complete seeds.",
        "", "## All scored candidates", "",
        "| Candidate | Parent | Score | Disposition |",
        "|---|---|---:|---|",
    ]
    for row in ranking["all_scores"]:  # type: ignore[index]
        ident = str(row["id"])
        item = by_id[ident]
        state = "selected" if ident in selected else "excluded by prototype" if "prototype_rejected" in item else "not selected"
        lines.append(f"| {ident} {item['slug']} | {item['parent']} | {float(row['score']):g} | {state} |")
    lines += [
        "", "## Independent ±50 percent sensitivity", "",
        "Each row changes just one weight. A tie at the tenth-place score keeps **all** tied candidates in that row; `retained` can therefore exceed ten. This does not change the declared baseline selection.",
        "", "| Axis | Factor | Enter | Leave | Tied cutoff | Retained |",
        "|---|---:|---|---|---|---:|",
    ]
    for item in ranking["sensitivity"]:  # type: ignore[index]
        enter = ", ".join(item["entered"]) or "—"
        leave = ", ".join(item["left"]) or "—"
        tied = "yes" if item["cutoff_tie"] else "no"
        lines.append(f"| {item['axis']} | {item['factor']} | {enter} | {leave} | {tied} | {item['retained_at_cutoff']} |")
    lines += [
        "", "**What does not follow:** the baseline top ten is not invariant under the declared weight perturbations. The H half-weight run replaces C25 with C18, while the N half-weight run keeps the baseline ten; these are two legal weightings with different and same selections. The computed table reports every axis and both directions.", "",
    ]
    (HERE / "selection.md").write_text("\n".join(lines), encoding="utf-8", newline="\n")
    print(f"rendered {len(candidates)} candidates and {len(selected)} selected packages")


if __name__ == "__main__":
    main()
