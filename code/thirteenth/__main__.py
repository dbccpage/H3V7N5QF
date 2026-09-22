"""`python -m thirteenth`: regenerate the computed files of `evidence/thirteenth/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from thirteenth.evidence import Plan, coarse_ok, coarses_ok, compare_evidence, ninth_ok, write_all


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one C-C1 exploration passes."""
    ninth = run["ninth_derivation"]
    coarses = run["coarses"]
    assert isinstance(ninth, dict) and isinstance(coarses, dict)
    coarse_holding = run["coarse_statements_holding_of_every_result"]
    rounds = run["rounds"]
    assert isinstance(coarse_holding, list) and isinstance(rounds, int)
    return bool(
        ninth_ok(ninth)
        and coarses_ok(coarses)
        and run["results_that_reach_what_is_given"] == 1
        and run["results_reached_from_what_is_given"] == run["results"]
        and run["two_term_rounds_equal_closed_form"] in (True, None)
        and run["empty_changes"] == 1
        and (rounds < 2 or coarses["determines_count"] >= 1)
        and (rounds < 3 or "determines_finer" not in coarse_holding or "both_relations" not in coarse_holding)
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="thirteenth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "thirteenth")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=defaults.bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--deep-bound", type=int, default=defaults.deep_bound)
    parser.add_argument("--deep-rounds", type=int, default=defaults.deep_rounds)
    parser.add_argument("--two-term-rounds", type=int, default=defaults.two_term_rounds)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--log-rounds", type=int, default=defaults.log_rounds)
    parser.add_argument("--coarse-bound", type=int, default=defaults.coarse_bound)
    parser.add_argument("--coarse-rounds", type=int, default=defaults.coarse_rounds)
    args = parser.parse_args(argv)
    plan = Plan(
        bound=args.bound,
        rounds=args.rounds,
        deep_bound=args.deep_bound,
        deep_rounds=args.deep_rounds,
        two_term_rounds=args.two_term_rounds,
        log_bound=args.log_bound,
        log_rounds=args.log_rounds,
        coarse_bound=args.coarse_bound,
        coarse_rounds=args.coarse_rounds,
    )
    differences: list[str] = []
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            summary = write_all(Path(tmp), plan)
            differences = compare_evidence(args.out, Path(tmp))
    else:
        summary = write_all(args.out, plan)
    runs = summary["runs"]
    coarse = summary["coarse"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(coarse, dict) and isinstance(given, dict)
    failed = False
    for tag, run in runs.items():
        assert isinstance(run, dict)
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = coarse_ok(coarse)
    failed = failed or not ok
    print(f"coarse: {coarse['coarse_results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = bool(given["r_and_s_same_coarser"]) and bool(given["r_and_s_differ_finer"]) and bool(given["empty_determines"])
    failed = failed or not ok
    print(f"given: r and s same coarser, differ finer, empty determines, checks {'pass' if ok else 'FAIL'}")
    if differences:
        failed = True
        print("check: " + "; ".join(differences))
    elif args.check:
        print("check: identical")
    return 1 if failed else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
