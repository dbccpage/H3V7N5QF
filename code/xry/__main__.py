"""`python -m xry`: regenerate the computed files of `evidence/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from xry.evidence import Plan, compare_evidence, write_all


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one exploration passes (an empty comparison does not count)."""
    agreeing = run["rounds_agreeing_with_unbounded_formula"]
    assert isinstance(agreeing, list)
    return bool(
        run["explored_equals_independent_count"]
        and run["round_equals_cost_formula_for_every_result"]
        and agreeing
        and all(agreeing)
        and not run["answers_reaching_something_new"]
        and run["frontier_entries_are_1_plus_2N_per_state_with_N_terms"]
    )


def shared_ok(summary: dict[str, object]) -> bool:
    """The checks that are not tied to one exploration pass."""
    given = summary["given"]
    assert isinstance(given, dict)
    return bool(
        not summary["free_cost_closed_form_mismatches"]
        and given["listed_builds_that_are_not_builds"] == 0
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="xry", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence"))
    parser.add_argument("--check", action="store_true")
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
    differences: list[str] = []
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            summary = write_all(Path(tmp), plan)
            differences = compare_evidence(args.out, Path(tmp))
    else:
        summary = write_all(args.out, plan)
    runs = summary["runs"]
    assert isinstance(runs, dict)
    failed = False
    for tag, run in runs.items():
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = shared_ok(summary)
    failed = failed or not ok
    print(f"given and free cost: checks {'pass' if ok else 'FAIL'}")
    for line in differences:
        print(line)
    if args.check:
        print(f"{args.out}: {'matches' if not differences else 'DIFFERS FROM'} a fresh regeneration")
    return 1 if failed or differences else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
