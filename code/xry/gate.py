"""`python -m xry.gate coverage.json`: line and branch coverage, each at least 95%.

`coverage` reports one combined figure; the task asks for both figures, so
they are read separately from the JSON report.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Mapping, Sequence
from pathlib import Path

THRESHOLD = 95.0


def rates(totals: Mapping[str, int]) -> tuple[float, float]:
    """(line %, branch %) from the `totals` of a coverage JSON report."""
    lines = 100.0 * totals["covered_lines"] / max(totals["num_statements"], 1)
    branches = 100.0 * totals["covered_branches"] / max(totals["num_branches"], 1)
    return lines, branches


def main(argv: Sequence[str] | None = None) -> int:
    """Print both rates; fail if either is below the threshold."""
    parser = argparse.ArgumentParser(prog="xry.gate", description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args(argv)
    totals = json.loads(args.report.read_text(encoding="utf-8"))["totals"]
    lines, branches = rates(totals)
    print(f"line coverage {lines:.2f}%, branch coverage {branches:.2f}%")
    return 0 if min(lines, branches) >= THRESHOLD else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
