"""`python -m twentyfourth`: write `evidence/twentyfourth/`, or check that it regenerates.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from twentyfourth.evidence import Plan, compare_evidence, write_all


def main(argv: Sequence[str] | None = None, plan: Plan | None = None) -> int:
    parser = argparse.ArgumentParser(prog="twentyfourth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence/twentyfourth"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    chosen = plan if plan is not None else Plan()
    if args.check:
        if not args.out.is_dir():
            print("missing evidence directory")
            return 1
        with tempfile.TemporaryDirectory() as tmp:
            fresh = Path(tmp) / "fresh"
            write_all(fresh, chosen)
            diffs = compare_evidence(args.out, fresh)
        if diffs:
            for line in diffs:
                print(line)
            return 1
        print("evidence/twentyfourth matches a fresh regeneration")
        return 0
    summary = write_all(args.out, chosen)
    print(f"wrote {args.out}; every check clean: {summary['every_check_clean']}")
    return 0 if summary["every_check_clean"] else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
