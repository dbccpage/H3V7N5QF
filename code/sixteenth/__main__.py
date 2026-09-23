"""`python -m sixteenth`: regenerate the computed files of `evidence/sixteenth/`.

With `--check`, regenerate into a temporary folder instead and compare the
result with `--out`, byte for byte, in both directions.
"""

from __future__ import annotations

import argparse
import tempfile
from collections.abc import Sequence
from pathlib import Path

from sixteenth.evidence import Plan, compare_evidence, ninth_ok, records_ok, write_all


def run_ok(run: dict[str, object]) -> bool:
    """Every check of one exploration passes."""
    ninth = run["ninth_derivation"]
    records = run["records"]
    rounds = run["rounds_agreeing_with_unbounded_series"]
    assert isinstance(ninth, dict) and isinstance(records, dict) and isinstance(rounds, list)
    return bool(
        run["explored_equals_independent_count"]
        and all(rounds)
        and run["one_term_rounds_equal_closed_form"]
        and run["two_term_rounds_equal_the_series"] in (True, None)
        and run["the_first_round_is_the_one_term_state_alone"] in (True, None)
        and run["attempts_equal_formula"]
        and run["admissions_equal_formula"]
        and run["frontier_entries_are_1_per_state_with_N_terms"]
        and records_ok(records)
        and run["results_with_a_two_change_cycle"] == run["results_with_a_term"] == int(str(run["results"])) - 1
        and run["results_with_exact_sequence_count"] == run["results"]
        and run["results_that_reach_what_is_given"] == 1
        and run["results_reached_from_what_is_given"] == run["results"]
        and ninth_ok(ninth)
        and run["statements_holding_in_every_result"] == []
    )


def reach_ok(reach: dict[str, object]) -> bool:
    """The reachability checks pass."""
    admits = reach["ordered_pairs_this_seed_admits_and_the_ninth_refuses"]
    assert isinstance(admits, list)
    return bool(
        reach["criterion_agrees_with_search"]
        and not admits
        and int(str(reach["ordered_pairs_the_ninth_admits_and_this_seed_refuses"])) > 0
        and reach["results_that_reach_what_is_given"] == 1
    )


def counts_ok(counts: dict[str, object]) -> bool:
    """The independent counts agree with the ninth's on the empty-record part and with the closed forms."""
    return bool(
        counts["empty_record_counts_are_the_ninth_counts"]
        and not counts["one_term_closed_form_mismatches"]
        and counts["product_equals_count_for_at_most_one_term"]
        and counts["count_exceeds_product_for_two_or_more_terms"]
    )


def given_ok(given: dict[str, object]) -> bool:
    """The witnesses of `given.json` stand."""
    return bool(
        given["changes_on_the_empty_state"] == 1
        and given["of_which_add_a_term"] == 1
        and given["same_relation_is_the_identity"]
        and given["other_relation_is_new"]
        and given["leftover_of_r_admitted_into_s"]
        and given["ninth_criterion_fails_on_ara"]
        and given["set_reading_breaks_the_identity"]
        and given["direct_additions_that_change_the_record"] == 0
    )


def alternatives_ok(alternatives: dict[str, object]) -> bool:
    """The unchosen readings behave as the paper says (D14).

    The set reading breaks the same-relation identity, and neither the ninth's
    criterion nor the carrying criterion agrees with search.  The drop reading
    keeps the identity and the ninth's criterion, and the carrying criterion
    does not agree with search.
    """
    as_set = alternatives["set"]
    drop = alternatives["drop"]
    assert isinstance(as_set, dict) and isinstance(drop, dict)
    set_reach = as_set["reachability"]
    drop_reach = drop["reachability"]
    assert isinstance(set_reach, dict) and isinstance(drop_reach, dict)
    return bool(
        as_set["explored_equals_independent_count"]
        and drop["explored_equals_independent_count"]
        and int(str(as_set["same_relation_identity_failures"])) > 0
        and drop["same_relation_identity_failures"] == 0
        and drop_reach["ninth_criterion_disagreements_with_search"] == 0
        and int(str(drop_reach["carrying_criterion_disagreements_with_search"])) > 0
        and int(str(set_reach["ninth_criterion_disagreements_with_search"])) > 0
        and int(str(set_reach["carrying_criterion_disagreements_with_search"])) > 0
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Write (or check) the evidence and print the one-line outcome of every check."""
    defaults = Plan()
    parser = argparse.ArgumentParser(prog="sixteenth", description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("evidence") / "sixteenth")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=defaults.bound)
    parser.add_argument("--rounds", type=int, default=defaults.rounds)
    parser.add_argument("--wide-bound", type=int, default=defaults.wide_bound)
    parser.add_argument("--wide-rounds", type=int, default=defaults.wide_rounds)
    parser.add_argument("--two-term-rounds", type=int, default=defaults.two_term_rounds)
    parser.add_argument("--log-bound", type=int, default=defaults.log_bound)
    parser.add_argument("--log-rounds", type=int, default=defaults.log_rounds)
    parser.add_argument("--reach-bound", type=int, default=defaults.reach_bound)
    parser.add_argument("--reach-rounds", type=int, default=defaults.reach_rounds)
    parser.add_argument("--reach-extra", type=int, default=defaults.reach_extra)
    parser.add_argument("--alt-bound", type=int, default=defaults.alt_bound)
    parser.add_argument("--alt-rounds", type=int, default=defaults.alt_rounds)
    parser.add_argument("--alt-reach-rounds", type=int, default=defaults.alt_reach_rounds)
    parser.add_argument("--alt-reach-extra", type=int, default=defaults.alt_reach_extra)
    parser.add_argument("--layers-upto", type=int, default=defaults.layers_upto)
    parser.add_argument("--count-upto", type=int, default=defaults.count_upto)
    parser.add_argument("--count-weight-upto", type=int, default=defaults.count_weight_upto)
    args = parser.parse_args(argv)
    plan = Plan(
        bound=args.bound,
        rounds=args.rounds,
        wide_bound=args.wide_bound,
        wide_rounds=args.wide_rounds,
        two_term_rounds=args.two_term_rounds,
        log_bound=args.log_bound,
        log_rounds=args.log_rounds,
        reach_bound=args.reach_bound,
        reach_rounds=args.reach_rounds,
        reach_extra=args.reach_extra,
        alt_bound=args.alt_bound,
        alt_rounds=args.alt_rounds,
        alt_reach_rounds=args.alt_reach_rounds,
        alt_reach_extra=args.alt_reach_extra,
        layers_upto=args.layers_upto,
        count_upto=args.count_upto,
        count_weight_upto=args.count_weight_upto,
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
    counts = summary["independent_counts"]
    given = summary["given"]
    alternatives = summary["alternatives"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(counts, dict)
    assert isinstance(given, dict) and isinstance(alternatives, dict)
    failed = False
    for tag, run in runs.items():
        assert isinstance(run, dict)
        ok = run_ok(run)
        failed = failed or not ok
        print(f"{tag}: {run['results']} results, checks {'pass' if ok else 'FAIL'}")
    for name, ok in (
        ("reachability", reach_ok(reach)),
        ("independent counts", counts_ok(counts)),
        ("given", given_ok(given)),
        ("alternatives", alternatives_ok(alternatives)),
    ):
        failed = failed or not ok
        print(f"{name}: checks {'pass' if ok else 'FAIL'}")
    if differences:
        failed = True
        print("check: " + "; ".join(differences))
    elif args.check:
        print("check: identical")
    return 1 if failed else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
