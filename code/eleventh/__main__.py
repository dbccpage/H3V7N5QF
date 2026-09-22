"""`python -m eleventh`: regenerate the computed files of `evidence/eleventh/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from eleventh.evidence import Plan, compare_evidence, labeled_ok, ninth_ok, writings_ok, write_all


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one C-W1 exploration passes."""
    ninth = run["ninth_derivation"]
    writings = run["writings"]
    assert isinstance(ninth, dict) and isinstance(writings, dict)
    writing_holding = run["writing_statements_holding_of_every_writing"]
    rounds = run["rounds"]
    assert isinstance(writing_holding, list) and isinstance(rounds, int)
    return bool(
        ninth_ok(ninth)
        and writings_ok(writings)
        and run["results_that_reach_what_is_given"] == 1
        and run["results_reached_from_what_is_given"] == run["results"]
        and run["two_term_rounds_equal_closed_form"] in (True, None)
        and run["empty_changes"] == 1
        and (rounds < 3 or bool(writings["r_not_s"]) or writings["colliding"] >= 0)
        and (rounds < 4 or "determines" not in writing_holding or "collides" not in writing_holding)
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="eleventh", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "eleventh")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=defaults.bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--deep-bound", type=int, default=defaults.deep_bound)
    parser.add_argument("--deep-rounds", type=int, default=defaults.deep_rounds)
    parser.add_argument("--two-term-rounds", type=int, default=defaults.two_term_rounds)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--log-rounds", type=int, default=defaults.log_rounds)
    parser.add_argument("--labeled-bound", type=int, default=defaults.labeled_bound)
    parser.add_argument("--labeled-rounds", type=int, default=defaults.labeled_rounds)
    args = parser.parse_args(argv)
    plan = Plan(
        bound=args.bound,
        rounds=args.rounds,
        deep_bound=args.deep_bound,
        deep_rounds=args.deep_rounds,
        two_term_rounds=args.two_term_rounds,
        log_bound=args.log_bound,
        log_rounds=args.log_rounds,
        labeled_bound=args.labeled_bound,
        labeled_rounds=args.labeled_rounds,
    )
    differences: list[str] = []
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            summary = write_all(Path(tmp), plan)
            differences = compare_evidence(args.out, Path(tmp))
    else:
        summary = write_all(args.out, plan)
    runs = summary["runs"]
    labeled = summary["labeled"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(labeled, dict) and isinstance(given, dict)
    failed = False
    for tag, run in runs.items():
        assert isinstance(run, dict)
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = labeled_ok(labeled)
    failed = failed or not ok
    print(f"labeled: {labeled['labeled_results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = bool(given["r_collision_not_s"]) and bool(given["identify_drops_a_term"])
    failed = failed or not ok
    print(f"given: r-collision not s, identify drops a term, checks {'pass' if ok else 'FAIL'}")
    if differences:
        failed = True
        print("check: " + "; ".join(differences))
    elif args.check:
        print("check: identical")
    return 1 if failed else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
