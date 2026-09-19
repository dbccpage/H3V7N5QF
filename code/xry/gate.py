"""`python -m xry.gate coverage.json`: line and branch coverage, and evidence fully covered.

Line and branch coverage each at least 95% -- `coverage` reports one combined
figure, and the task asks for both, so they are read separately from the JSON
report.

On top of the 95% floor, every `code/**/evidence.py` must be *fully* covered,
line and branch.  Each derivation's `evidence.py` holds families of
differential checks: a computed value against a closed form, a criterion
against a search, one derivation against the last.  Each such check has a
branch that records a disagreement, and on correct code that branch never
runs -- so it is dead, and a regression that makes the check vacuous passes
green.  The guard against that is an injection test that forces the
disagreement and proves the branch fires; the discipline is that every check
has one.  It slipped in three successive derivations, each shipping a check
whose failure branch no test drove, caught only by a reader watching the
coverage of one file.  This gate makes that a hard failure instead: a dead
branch is an uncovered line, and an evidence module is not allowed to have
one.  A line that is genuinely unreachable is exempted deliberately with
`# pragma: no cover`, never left silently uncovered.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

THRESHOLD = 95.0


def rates(totals: Mapping[str, int]) -> tuple[float, float]:
    """(line %, branch %) from the `totals` of a coverage JSON report."""
    lines = 100.0 * totals["covered_lines"] / max(totals["num_statements"], 1)
    branches = 100.0 * totals["covered_branches"] / max(totals["num_branches"], 1)
    return lines, branches


def uncovered_evidence(report: Mapping[str, Any]) -> dict[str, str]:
    """`code/**/evidence.py` modules with a line or branch no test ran, path -> what is missing.

    A dead differential-check branch -- a disagreement or mismatch path that no
    input triggers -- is exactly such a line.  Requiring the evidence modules to
    be fully covered turns it into a gate failure until an injection test drives
    the branch, or a deliberate `# pragma: no cover` marks it unreachable.
    """
    out: dict[str, str] = {}
    for path, data in report.get("files", {}).items():
        name = path.replace("\\", "/")
        if not name.endswith("evidence.py"):
            continue
        summary = data["summary"]
        if summary["missing_lines"] or summary.get("missing_branches", 0):
            lines = sorted(data.get("missing_lines", []))
            branches = sorted(data.get("missing_branches", []))
            out[name] = f"missing lines {lines}, missing branches {branches}"
    return out


def main(argv: Sequence[str] | None = None) -> int:
    """Print both rates; fail if either is below the threshold or an evidence module is not fully covered."""
    parser = argparse.ArgumentParser(prog="xry.gate", description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args(argv)
    report = json.loads(args.report.read_text(encoding="utf-8"))
    lines, branches = rates(report["totals"])
    print(f"line coverage {lines:.2f}%, branch coverage {branches:.2f}%")
    ok = min(lines, branches) >= THRESHOLD
    for name, missing in sorted(uncovered_evidence(report).items()):
        print(f"evidence not fully covered: {name} -- {missing} (add an injection test, or mark it # pragma: no cover)")
        ok = False
    return 0 if ok else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
