"""`python -m seventeenth`: regenerate `evidence/seventeenth/`.

With `--check`, regenerate into a temporary folder and compare with `--out`.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from xry.evidence import compare_evidence

from seventeenth.evidence import Plan, write_all


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="seventeenth")
    parser.add_argument("--out", type=Path, default=Path("evidence/seventeenth"))
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=None)
    parser.add_argument("--rounds", type=int, default=None)
    args = parser.parse_args(list(argv) if argv is not None else None)
    plan = Plan(
        bound=Plan.bound if args.bound is None else args.bound,
        rounds=Plan.rounds if args.rounds is None else args.rounds,
    )
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            fresh = Path(tmp) / "fresh"
            summary = write_all(fresh, plan)
            diffs = compare_evidence(args.out, fresh)
        if diffs or summary.get("passes") is not True:
            for line in diffs:
                print(line)
            return 1
        print("evidence/seventeenth matches a fresh regeneration")
        return 0
    summary = write_all(args.out, plan)
    if summary.get("passes") is not True:
        print("seventeenth checks failed")
        return 1
    print(f"wrote {args.out}")
    return 0
