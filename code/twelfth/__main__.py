"""`python -m twelfth`: regenerate the computed files of `evidence/twelfth/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from twelfth.evidence import Plan, compare_evidence, ninth_ok, recorded_ok, records_ok, write_all


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one C-M1 exploration passes."""
    ninth = run["ninth_derivation"]
    records = run["records"]
    assert isinstance(ninth, dict) and isinstance(records, dict)
    record_holding = run["record_statements_holding_of_every_identification"]
    rounds = run["rounds"]
    assert isinstance(record_holding, list) and isinstance(rounds, int)
    return bool(
        ninth_ok(ninth)
        and records_ok(records)
        and run["results_that_reach_what_is_given"] == 1
        and run["results_reached_from_what_is_given"] == run["results"]
        and run["two_term_rounds_equal_closed_form"] in (True, None)
        and run["empty_changes"] == 1
        and (rounds < 3 or records["identifications"] == 0 or bool(records["differs"]) or bool(records["empty_records"]))
        and (rounds < 4 or "empty_record" not in record_holding or "nonempty_record" not in record_holding)
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="twelfth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "twelfth")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=defaults.bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--deep-bound", type=int, default=defaults.deep_bound)
    parser.add_argument("--deep-rounds", type=int, default=defaults.deep_rounds)
    parser.add_argument("--two-term-rounds", type=int, default=defaults.two_term_rounds)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--log-rounds", type=int, default=defaults.log_rounds)
    parser.add_argument("--recorded-bound", type=int, default=defaults.recorded_bound)
    parser.add_argument("--recorded-rounds", type=int, default=defaults.recorded_rounds)
    args = parser.parse_args(argv)
    plan = Plan(
        bound=args.bound,
        rounds=args.rounds,
        deep_bound=args.deep_bound,
        deep_rounds=args.deep_rounds,
        two_term_rounds=args.two_term_rounds,
        log_bound=args.log_bound,
        log_rounds=args.log_rounds,
        recorded_bound=args.recorded_bound,
        recorded_rounds=args.recorded_rounds,
    )
    differences: list[str] = []
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            summary = write_all(Path(tmp), plan)
            differences = compare_evidence(args.out, Path(tmp))
    else:
        summary = write_all(args.out, plan)
    runs = summary["runs"]
    recorded = summary["recorded"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(recorded, dict) and isinstance(given, dict)
    failed = False
    for tag, run in runs.items():
        assert isinstance(run, dict)
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = recorded_ok(recorded)
    failed = failed or not ok
    print(f"recorded: {recorded['recorded_results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = bool(given["r_record_not_s"]) and bool(given["identify_drops_a_term"]) and bool(given["empty_restored"])
    failed = failed or not ok
    print(f"given: r-record not s, identify drops a term, empty restored, checks {'pass' if ok else 'FAIL'}")
    if differences:
        failed = True
        print("check: " + "; ".join(differences))
    elif args.check:
        print("check: identical")
    return 1 if failed else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
