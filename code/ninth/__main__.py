"""`python -m ninth`: regenerate the computed files of `evidence/ninth/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from ninth.evidence import Plan, compare_evidence, eighth_ok, seventh_ok, write_all


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one exploration passes (an empty comparison does not count)."""
    agreeing = run["rounds_agreeing_with_unbounded_formula"]
    seventh = run["seventh_derivation"]
    eighth = run["eighth_derivation"]
    assert isinstance(agreeing, list) and isinstance(seventh, dict) and isinstance(eighth, dict)
    return bool(
        run["explored_equals_independent_count"]
        and run["round_equals_cost_formula_for_every_result"]
        and run["cost_is_the_seventh_cost_of_either_part_plus_the_other_total"]
        and run["sum_of_the_part_costs_exceeds_the_cost_by_the_terms"]
        and run["relations_agreeing_equal_closed_form"]
        and agreeing
        and all(agreeing)
        and run["two_term_rounds_equal_closed_form"] in (True, None)
        and run["the_first_round_is_the_one_term_state_alone"] in (True, None)
        and run["attempts_equal_formula"]
        and run["xrx_making_equal_eighth_formula"]
        and run["xsx_making_equal_eighth_formula"]
        and not run["cost_raised_by_more_than_one"]
        and not run["size_not_moved_by_one"]
        and not run["cost_rule_disagreements"]
        and not run["term_lost"]
        and run["changes_keeping_the_round"] == 0
        and run["frontier_entries_are_1_per_state_with_N_terms"]
        and run["results_with_a_two_change_cycle"] == run["results_with_a_term"] == int(str(run["results"])) - 1
        and run["results_with_exact_sequence_count"] == run["results"]
        and run["one_term_results_follow_the_binomial"]
        and run["results_that_reach_what_is_given"] == 1
        and run["results_reached_from_what_is_given"] == run["results"]
        and run["statements_holding_in_every_result"] == []
        and seventh_ok(seventh)
        and all(eighth_ok(block) for block in eighth.values())
    )


def reach_ok(reach: dict[str, object]) -> bool:
    """The criterion agrees with the search and with the earlier criteria on a non-empty set of pairs."""
    return bool(
        reach["criterion_agrees_with_search"]
        and reach["ordered_pairs"]
        and reach["unordered_pairs_reachable_both_ways"] != 0
        and reach["results_that_reach_what_is_given"] == 1
        and reach["seventh_criterion_on_either_part_agrees_on_every_pair"]
        and reach["eighth_criterion_agrees_on_results_with_a_term"]
        and reach["ordered_pairs_of_results_with_a_term"]
    )


def census_ok(census: dict[str, object]) -> bool:
    """The counts-only run agrees with the independent count, the cost formula, the seventh's and the eighth's."""
    seventh = census["seventh_derivation"]
    eighth = census["eighth_derivation"]
    assert isinstance(seventh, dict) and isinstance(eighth, dict)
    return bool(
        census["explored_equals_independent_count"]
        and census["round_equals_cost_formula_for_every_result"]
        and census["one_term_results_follow_the_binomial"]
        and seventh_ok(seventh)
        and all(eighth_ok(block) for block in eighth.values())
    )


def shared_ok(summary: dict[str, object]) -> bool:
    """The checks that are not tied to one exploration pass."""
    given = summary["given"]
    counts = summary["independent_counts"]
    assert isinstance(given, dict) and isinstance(counts, dict)
    return bool(
        given["changes_on_the_empty_state"] == given["of_which_add_a_term"] == 1
        and given["attempts_not_performed"] == 0
        and not counts["two_term_closed_form_mismatches"]
        and counts["eighth_counts_by_destroyed_givens_add_up_to_these"]
        and counts["product_equals_count_for_at_most_one_term"]
        and counts["count_exceeds_product_for_two_or_more_terms"]
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="ninth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "ninth")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=defaults.bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--census-bound", type=int, default=defaults.census_bound)
    parser.add_argument("--census-rounds", type=int, default=defaults.census_rounds)
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
        bound=args.bound,
        rounds=args.rounds,
        census_bound=args.census_bound,
        census_rounds=args.census_rounds,
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
    census = summary["census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    failed = False
    for tag, run in runs.items():
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = reach_ok(reach)
    failed = failed or not ok
    print(f"reachability: {reach['ordered_pairs']} pairs, checks {'pass' if ok else 'FAIL'}")
    for tag, count in census.items():
        ok = census_ok(count)
        failed = failed or not ok
        print(f"census {tag}: {count['results']} results, checks {'pass' if ok else 'FAIL'}")
    ok = shared_ok(summary)
    failed = failed or not ok
    print(f"given and counts: checks {'pass' if ok else 'FAIL'}")
    for line in differences:
        print(line)
    if args.check:
        print(f"{args.out}: {'matches' if not differences else 'DIFFERS FROM'} a fresh regeneration")
    return 1 if failed or differences else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
