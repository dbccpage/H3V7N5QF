"""`python -m nineteenth`: write `evidence/nineteenth/` or check it regenerates."""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from xry.evidence import compare_evidence

from nineteenth.evidence import write_all


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="nineteenth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence/nineteenth"))
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=3)
    parser.add_argument("--rounds", type=int, default=12)
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.check:
        if not args.out.is_dir():
            print("missing evidence directory")
            return 1
        with tempfile.TemporaryDirectory() as tmp:
            fresh = Path(tmp) / "fresh"
            write_all(fresh, args.bound, args.rounds)
            diffs = compare_evidence(args.out, fresh)
        if diffs:
            for line in diffs:
                print(line)
            return 1
        print("evidence/nineteenth matches a fresh regeneration")
        return 0
    write_all(args.out, args.bound, args.rounds)
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
