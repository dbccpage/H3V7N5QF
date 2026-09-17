"""`python -m xry`: regenerate the computed files of `evidence/`."""

from __future__ import annotations

import argparse
from collections.abc import Sequence
from pathlib import Path

from xry.evidence import Plan, write_all


def main(argv: Sequence[str] | None = None) -> int:
    """Write the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="xry", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence"))
    parser.add_argument("--free-bound", type=int, default=defaults.free_bound)
    parser.add_argument("--anchored-bound", type=int, default=defaults.anchored_bound)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--layers-upto", type=int, default=defaults.layers_upto)
    parser.add_argument("--count-upto", type=int, default=defaults.count_upto)
    args = parser.parse_args(argv)
    plan = Plan(
        free_bound=args.free_bound,
        anchored_bound=args.anchored_bound,
        log_bound=args.log_bound,
        rounds=args.rounds,
        layers_upto=args.layers_upto,
        count_upto=args.count_upto,
    )
    summary = write_all(args.out, plan)
    runs = summary["runs"]
    assert isinstance(runs, dict)
    failed = False
    for tag, run in runs.items():
        ok = (
            run["explored_equals_independent_count"]
            and run["round_equals_cost_formula_for_every_result"]
            and all(run["rounds_agreeing_with_unbounded_formula"])
            and not run["answers_reaching_something_new"]
        )
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    return 1 if failed else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
