"""`python -m third`: regenerate the computed files of `evidence/third/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from third.evidence import Plan, compare_evidence, write_all

SAME_AS_SECOND = "same_results_rounds_and_attempts_as_second_derivation_without_identifications"


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one exploration passes (an empty comparison does not count)."""
    agreeing = run["rounds_agreeing_with_unbounded_formula"]
    assert isinstance(agreeing, list)
    return bool(
        run["explored_equals_independent_count"]
        and run["round_equals_cost_formula_for_every_result"]
        and agreeing
        and all(agreeing)
        and run[SAME_AS_SECOND]
        and run["additions_never_negative"]
        and run["attempts_equal_formula_1_plus_n_squared_minus_m"]
        and run["obstructed_equal_formula_n"]
        and not run["answers_reaching_something_new"]
        and run["answers_removing_the_obstruction"] == 0
        and not run["round_not_raised_by_one"]
        and not run["counts_lowered_by"]
        and not run["fewest_classes_lowered_by"]
        and run["frontier_entries_are_1_plus_2N_per_state_with_N_terms"]
        and run["results_that_reach_what_is_given"] == 1
    )


def reach_ok(reach: dict[str, object]) -> bool:
    """Containment agrees with the search on a non-empty set of pairs, one way only, within the second's."""
    return bool(
        reach["embedding_agrees_with_search"]
        and reach["ordered_pairs"]
        and reach["unordered_pairs_reachable_both_ways"] == 0
        and reach["pairs_reachable_here_but_not_under_second_seed"] == 0
    )


def census_ok(census: dict[str, object]) -> bool:
    """The counts-only run agrees with the independent count, the cost formula, and the second's."""
    return bool(
        census["explored_equals_independent_count"]
        and census["round_equals_cost_formula_for_every_result"]
        and census[SAME_AS_SECOND]
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
    parser = argparse.ArgumentParser(prog="third", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "third")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--free-bound", type=int, default=defaults.free_bound)
    parser.add_argument("--anchored-bound", type=int, default=defaults.anchored_bound)
    parser.add_argument("--census-bound", type=int, default=defaults.census_bound)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--reach-bound", type=int, default=defaults.reach_bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--layers-upto", type=int, default=defaults.layers_upto)
    parser.add_argument("--count-upto", type=int, default=defaults.count_upto)
    args = parser.parse_args(argv)
    plan = Plan(
        free_bound=args.free_bound,
        anchored_bound=args.anchored_bound,
        census_bound=args.census_bound,
        log_bound=args.log_bound,
        reach_bound=args.reach_bound,
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
    reach = summary["reachability"]
    census = summary["anchored_census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    failed = False
    for tag, run in runs.items():
        ok = run_ok(run) and reach_ok(reach[tag])
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    for tag, count in census.items():
        ok = census_ok(count)
        failed = failed or not ok
        print(
            f"{tag} census at bound {count['bound_on_terms']}: {count['results']} results, "
            f"checks {'pass' if ok else 'FAIL'}"
        )
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
