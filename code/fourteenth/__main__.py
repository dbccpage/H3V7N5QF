"""`python -m fourteenth`: regenerate the computed files of `evidence/fourteenth/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from fourteenth.evidence import Plan, compare_evidence, leftovers_ok, ninth_ok, tagged_ok, write_all


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one C-F1 exploration passes."""
    ninth = run["ninth_derivation"]
    leftovers = run["leftovers"]
    assert isinstance(ninth, dict) and isinstance(leftovers, dict)
    leftover_holding = run["leftover_statements_holding_of_every_change"]
    rounds = run["rounds"]
    assert isinstance(leftover_holding, list) and isinstance(rounds, int)
    return bool(
        ninth_ok(ninth)
        and leftovers_ok(leftovers)
        and run["results_that_reach_what_is_given"] == 1
        and run["results_reached_from_what_is_given"] == run["results"]
        and run["two_term_rounds_equal_closed_form"] in (True, None)
        and run["empty_changes"] == run["empty_nothing"] == 1
        and (rounds < 4 or bool(leftovers["three_kinds_inhabited"]))
        and (rounds < 4 or "leaves_nothing" not in leftover_holding)
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="fourteenth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "fourteenth")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=defaults.bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--deep-bound", type=int, default=defaults.deep_bound)
    parser.add_argument("--deep-rounds", type=int, default=defaults.deep_rounds)
    parser.add_argument("--two-term-rounds", type=int, default=defaults.two_term_rounds)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--log-rounds", type=int, default=defaults.log_rounds)
    parser.add_argument("--tagged-bound", type=int, default=defaults.tagged_bound)
    parser.add_argument("--tagged-rounds", type=int, default=defaults.tagged_rounds)
    args = parser.parse_args(argv)
    plan = Plan(
        bound=args.bound,
        rounds=args.rounds,
        deep_bound=args.deep_bound,
        deep_rounds=args.deep_rounds,
        two_term_rounds=args.two_term_rounds,
        log_bound=args.log_bound,
        log_rounds=args.log_rounds,
        tagged_bound=args.tagged_bound,
        tagged_rounds=args.tagged_rounds,
    )
    differences: list[str] = []
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            summary = write_all(Path(tmp), plan)
            differences = compare_evidence(args.out, Path(tmp))
    else:
        summary = write_all(args.out, plan)
    runs = summary["runs"]
    tagged = summary["tagged"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(tagged, dict) and isinstance(given, dict)
    failed = False
    for tag, run in runs.items():
        assert isinstance(run, dict)
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = tagged_ok(tagged)
    failed = failed or not ok
    print(f"tagged: {tagged['tagged_results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = bool(given["r_and_s_same_leftover"]) and bool(given["leftover_not_assertion"]) and bool(given["leftover_not_answer"])
    failed = failed or not ok
    print(f"given: leftover of r is leftover of s, not an assertion, not an answer, checks {'pass' if ok else 'FAIL'}")
    if differences:
        failed = True
        print("check: " + "; ".join(differences))
    elif args.check:
        print("check: identical")
    return 1 if failed else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
