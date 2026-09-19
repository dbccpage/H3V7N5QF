"""`python -m eighth`: regenerate the computed files of `evidence/eighth/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from eighth.evidence import Plan, compare_evidence, write_all

SAME_RESULTS = "same_results_and_rounds_as_sixth_derivation"
SAME_SEQUENCES = "same_shortest_sequence_counts_as_sixth_derivation"


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one exploration passes (an empty comparison does not count)."""
    agreeing = run["rounds_agreeing_with_unbounded_formula"]
    assert isinstance(agreeing, list)
    return bool(
        run["explored_equals_independent_count"]
        and run["round_equals_cost_formula_for_every_result"]
        and agreeing
        and all(agreeing)
        and run["two_term_rounds_equal_closed_form"] in (True, None)
        and run[SAME_RESULTS]
        and run[SAME_SEQUENCES]
        and run["results_asserting_nothing_with_s"] != run["results"]
        and run["attempts_equal_formula"]
        and run["xrx_making_equal_sixth_formula"]
        and run["xsx_making_equal_sixth_formula"]
        and not run["cost_raised_by_more_than_one"]
        and not run["cost_rule_disagreements"]
        and not run["names_told_apart_again"]
        and run["changes_keeping_the_round"] == 0
        and run["frontier_entries_are_1_per_state_with_N_terms"]
        and run["results_with_a_two_change_cycle"] == run["results"]
        and run["two_term_sequences_equal_multinomial"] in (True, None)
        and run["results_that_reach_what_is_given"] != 1
        and run["statements_holding_in_every_result"] == ["at_least_one_term_r", "at_least_one_term_s"]
    )


def reach_ok(reach: dict[str, object]) -> bool:
    """The criterion agrees with the search on a non-empty set of pairs; the `s` part imposes nothing."""
    return bool(
        reach["criterion_agrees_with_search"]
        and reach["ordered_pairs"]
        and reach["unordered_pairs_reachable_both_ways"] != 0
        and reach["ordered_pairs_with_the_same_r_part"] == reach["of_which_reachable_both_ways"] != 0
    )


def census_ok(census: dict[str, object]) -> bool:
    """The counts-only run agrees with the independent count, the cost formula, and the sixth's."""
    return bool(
        census["explored_equals_independent_count"]
        and census["round_equals_cost_formula_for_every_result"]
        and census[SAME_RESULTS]
        and census[SAME_SEQUENCES]
    )


def shared_ok(summary: dict[str, object]) -> bool:
    """The checks that are not tied to one exploration pass."""
    given = summary["given"]
    counts = summary["independent_counts"]
    assert isinstance(given, dict) and isinstance(counts, dict)
    return bool(
        not summary["free_cost_closed_form_mismatches"]
        and given["attempts_not_performed"] == 0
        and given["beginnings_whose_loop_counts_differ_from_formula"] == 0
        and counts["product_equals_count_for_one_term"]
        and counts["count_exceeds_product_for_two_or_more_terms"]
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="eighth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "eighth")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--free-bound", type=int, default=defaults.free_bound)
    parser.add_argument("--anchored-bound", type=int, default=defaults.anchored_bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--census-bound", type=int, default=defaults.census_bound)
    parser.add_argument("--deep-bound", type=int, default=defaults.deep_bound)
    parser.add_argument("--deep-rounds", type=int, default=defaults.deep_rounds)
    parser.add_argument("--two-term-rounds", type=int, default=defaults.two_term_rounds)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--log-rounds", type=int, default=defaults.log_rounds)
    parser.add_argument("--reach-bound", type=int, default=defaults.reach_bound)
    parser.add_argument("--reach-rounds", type=int, default=defaults.reach_rounds)
    parser.add_argument("--reach-extra", type=int, default=defaults.reach_extra)
    parser.add_argument("--layers-upto", type=int, default=defaults.layers_upto)
    parser.add_argument("--count-upto", type=int, default=defaults.count_upto)
    parser.add_argument("--count-total-upto", type=int, default=defaults.count_total_upto)
    args = parser.parse_args(argv)
    plan = Plan(
        free_bound=args.free_bound,
        anchored_bound=args.anchored_bound,
        rounds=args.rounds,
        census_bound=args.census_bound,
        deep_bound=args.deep_bound,
        deep_rounds=args.deep_rounds,
        two_term_rounds=args.two_term_rounds,
        log_bound=args.log_bound,
        log_rounds=args.log_rounds,
        reach_bound=args.reach_bound,
        reach_rounds=args.reach_rounds,
        reach_extra=args.reach_extra,
        layers_upto=args.layers_upto,
        count_upto=args.count_upto,
        count_total_upto=args.count_total_upto,
    )
    differences: list[str] = []
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            summary = write_all(Path(tmp), plan)
            differences = compare_evidence(args.out, Path(tmp))
    else:
        summary = write_all(args.out, plan)
    runs = summary["runs"]
    reach = summary["reachability"]
    census = summary["anchored_census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    failed = False
    for tag, run in runs.items():
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    for tag, pairs in reach.items():
        ok = reach_ok(pairs)
        failed = failed or not ok
        print(f"{tag} reachability: {pairs['ordered_pairs']} pairs, checks {'pass' if ok else 'FAIL'}")
    for tag, count in census.items():
        ok = census_ok(count)
        failed = failed or not ok
        print(f"{tag} census at bound {count['bound_on_terms']}: {count['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = shared_ok(summary)
    failed = failed or not ok
    print(f"given, counts and free cost: checks {'pass' if ok else 'FAIL'}")
    for line in differences:
        print(line)
    if args.check:
        print(f"{args.out}: {'matches' if not differences else 'DIFFERS FROM'} a fresh regeneration")
    return 1 if failed or differences else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
