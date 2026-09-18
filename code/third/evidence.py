"""Writes `evidence/third/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_third.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest, `compare_evidence`,
    `states_on_given_terms`, `alternative`, `added_rows` and `frontier_rows`
    do not depend on the kinds of change.

Cited from the second derivation (`second.evidence`) and re-checked
    `Plan` (the same bounds), `write_counts` (the independent counts of the
    results, the same set under both seeds) and `check_free_cost` (the FREE
    closed form against the best placement; the same functions) mention no
    change.  The second derivation's exploration with identifications left
    out is run here beside the third exploration and the two are compared
    result by result and round by round (`write_run`, `write_census`); its
    carrying-map reachability is compared pair by pair with reachability by
    containment (`write_reach`).  `attempt_record`, `result_rows`,
    `write_given`, `write_run`, `check_changes` and `write_reach` are written
    afresh because they list changes, answers and reachability.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from second.evidence import Plan, _by_terms, _counted, check_free_cost, write_counts
from second.explore import explore as explore_second
from second.reach import reachable as reachable_second
from xry.evidence import (
    _write_csv,
    _write_json,
    added_rows,
    alternative,
    compare_evidence,
    frontier_rows,
    states_on_given_terms,
    write_manifest,
)
from xry.explore import Attempt, Exploration, order
from xry.state import Sameness, State, added, canonical, given

from third.changes import (
    REMOVAL_IMPOSSIBLE,
    Answer,
    Kind,
    attempt_counts,
    changes,
    is_build_of,
    obstruction,
    one_term_builds,
)
from third.cost import cost
from third.explore import check_answers, count_sequences, explore, performed, removal_answers
from third.follows import verdicts
from third.invariants import fewest_classes, never_decreases
from third.orbits import layer_counts
from third.reach import embedding, reachable, reachable_by_search

__all__ = [
    "ChangeCheck",
    "Plan",
    "attempt_record",
    "check_changes",
    "check_free_cost",
    "compare_evidence",
    "result_rows",
    "same_as_second",
    "write_all",
    "write_census",
    "write_counts",
    "write_given",
    "write_log",
    "write_reach",
    "write_run",
]


def _further_written(state: State, ans: Answer) -> list[str]:
    """The further changes of an answer, in words (an added term is written as in the result)."""
    return [
        c.written(ans.result if max(c.x, c.y) >= state.n else state) for c in ans.further
    ]


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change, the obstruction, the answers.

    For an obstructed change the record also declares why "remove the
    obstruction" is not an answer under this seed.
    """
    w = rec.state.term_writing()
    return {
        "state": rec.state.key(),
        "written": rec.state.written(),
        "round": round_,
        "change": rec.change.written(rec.state),
        "adds": list(rec.change.additions),
        "obstruction": [f"{w[x]}r{w[y]}" for x, y in rec.obstruction],
        "outcome": None if rec.outcome is None else rec.outcome.key(),
        "beyond_bound": rec.beyond,
        "remove_the_obstruction": REMOVAL_IMPOSSIBLE if rec.obstruction else None,
        "answers": [
            {
                "answer": ans.kind.value,
                "further": _further_written(rec.state, ans),
                "completes_the_change": ans.completes,
                "changes_performed": ans.performed,
                "result": canonical(ans.result).key(),
            }
            for ans in rec.answers
        ],
    }


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the alternatives for what is given, and every attempt on them."""
    found = states_on_given_terms()
    doc: dict[str, object] = {
        "legal_states_on_the_given_terms_with_arb": [s.written() for s in found],
        "count": len(found),
    }
    not_builds = 0
    for sameness in Sameness:
        for bra in (False, True):
            start = given(bra, sameness)
            expl = explore(start, bound=3, rounds=1, keep_log=True)
            builds = {}
            for change in changes(start):
                if obstruction(start, change):
                    all_builds = one_term_builds(start, change.x)
                    not_builds += sum(1 for b in all_builds if not is_build_of(b, start, change))
                    distinct = sorted({canonical(b) for b in all_builds}, key=order)
                    builds[change.written(start)] = {
                        "one_term_builds": len(all_builds),
                        "up_to_sameness": [b.written() for b in distinct],
                    }
            one = State.of(1, [], None if sameness is Sameness.FREE else (0, 0))
            attempts, obstructed = attempt_counts(start)
            doc[f"{sameness.value}/{alternative(bra)}"] = {
                "state": start.written(),
                "changes": attempts,
                "of_which_obstructed": obstructed,
                "attempts": [attempt_record(rec, 1) for rec in expl.log],
                "builds_with_one_added_term": builds,
                "reaches_the_other_beginning": reachable(start, given(not bra, sameness)),
                "reaches_the_one_term_state": reachable(start, one),
            }
    _write_json(out / "given.json", doc)
    return {"states_on_given_terms": len(found), "listed_builds_that_are_not_builds": not_builds}


def result_rows(expl: Exploration, bra: bool, sequences: dict[State, int]) -> list[list[object]]:
    """One row per result: additions, round, cost, classes, attempts, sequences, return."""
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        terms, assertions = added(state)
        attempts, obstructed = attempt_counts(state)
        c = cost(state, bra)
        rows.append(
            [
                state.key(),
                state.written(),
                state.n,
                state.m,
                terms,
                assertions,
                expl.depth[state],
                "" if c is None else c,
                fewest_classes(state),
                attempts,
                obstructed,
                sequences[state],
                int(reachable(state, expl.start)),
            ]
        )
    return rows


RESULT_HEADER = (
    "state",
    "written",
    "terms",
    "assertions",
    "terms_added_to_given",
    "assertions_added_to_given",
    "round_first_reached",
    "fewest_changes_by_formula",
    "fewest_classes",
    "changes_attempted",
    "obstructed_additions",
    "sequences_of_changes",
    "reaches_what_is_given",
)


@dataclass(frozen=True)
class ChangeCheck:
    """What `check_changes` found on every unobstructed change within the bound."""

    checked: int
    round_not_raised_by_one: tuple[str, ...]
    counts_lowered_by: tuple[str, ...]
    fewest_classes_lowered_by: tuple[str, ...]


def check_changes(expl: Exploration) -> ChangeCheck:
    """On every unobstructed change within the bound: the round rises by one, no count falls.

    Checks that the outcome's round is the state's plus one, that terms and
    assertions do not decrease while the size rises by one, and that the
    fewest classes do not decrease.
    """
    known: dict[State, int] = {}

    def classes(state: State) -> int:
        if state not in known:
            known[state] = fewest_classes(state)
        return known[state]

    checked = 0
    round_off: list[str] = []
    lowered: list[str] = []
    classes_lowered: list[str] = []
    for state, change, out in performed(expl):
        checked += 1
        name = f"{state.key()} / {change.written(state)}"
        if expl.depth[out] != expl.depth[state] + 1:
            round_off.append(name)
        if not never_decreases(state, out):
            lowered.append(name)
        if classes(out) < classes(state):
            classes_lowered.append(name)
    return ChangeCheck(checked, tuple(round_off), tuple(lowered), tuple(classes_lowered))


def same_as_second(expl: Exploration, second: Exploration) -> bool:
    """Do two explorations agree on results, rounds, attempts and obstructions?"""
    return (
        expl.depth == second.depth
        and expl.new_per_round == second.new_per_round
        and expl.attempts_per_round == second.attempts_per_round
        and expl.obstructed_per_round == second.obstructed_per_round
    )


def _formula_counts(expl: Exploration) -> tuple[int, int]:
    """Attempts and obstructed attempts on every result whose changes were attempted."""
    tried = [s for s, r in expl.depth.items() if r < expl.rounds]
    return sum(attempt_counts(s)[0] for s in tried), sum(attempt_counts(s)[1] for s in tried)


def write_run(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> dict[str, object]:
    """All files of one exploration; returns its summary."""
    tag = f"{sameness.value}_{alternative(bra)}"
    bound = plan.bound(sameness)
    start = given(bra, sameness)
    expl = explore(start, bound, plan.rounds)
    second = explore_second(start, bound, plan.rounds, additions_only=True)
    sequences = count_sequences(expl)

    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, bra, sequences))
    _write_csv(
        out / f"added_{tag}.csv",
        ("terms_added_to_given", "assertions_added_to_given", "results", "first_round", "last_round"),
        added_rows(expl),
    )
    _write_csv(
        out / f"frontier_{tag}.csv",
        ("state", "written", "round_first_reached", "leaves_by_the_change", "leaves_by_a_build"),
        frontier_rows(expl),
    )

    exact = layer_counts(sameness, bra, plan.layers_upto)
    so_far = 0
    round_rows: list[list[object]] = []
    for r in range(plan.rounds + 1):
        so_far += expl.new_per_round[r]
        round_rows.append(
            [
                r,
                expl.new_per_round[r],
                so_far,
                expl.attempts_per_round[r],
                expl.obstructed_per_round[r],
                second.new_per_round[r],
                exact[r] if r < len(exact) else "",
            ]
        )
    _write_csv(
        out / f"rounds_{tag}.csv",
        (
            "round",
            "new_results_within_bound",
            "results_so_far_within_bound",
            "changes_attempted_so_far",
            "of_which_obstructed",
            "new_results_second_derivation_without_identifications",
            "new_results_without_bound_by_formula",
        ),
        round_rows,
    )

    found = verdicts(expl)
    _write_csv(
        out / f"follows_{tag}.csv",
        ("statement", "wording", "in_what_is_given", "first_holds", "round", "first_fails", "round_"),
        [
            [
                v.statement,
                v.wording,
                int(v.in_given),
                "" if v.holds_at is None else v.holds_at.written(),
                "" if v.holds_round is None else v.holds_round,
                "" if v.fails_at is None else v.fails_at.written(),
                "" if v.fails_round is None else v.fails_round,
            ]
            for v in found
        ],
    )

    by_terms = _by_terms(expl)
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    # Rounds 0 .. N - 2 are complete within the bound; only rounds that were run can be compared.
    within_bound_layers = min(plan.layers_upto, bound - 2, plan.rounds)
    check = check_answers(expl)
    entries: dict[State, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s in expl.depth if s.n == bound}
    one_plus_two_n = set(entries) == full and all(c == 1 + 2 * s.n for s, c in entries.items())
    edges = check_changes(expl)
    attempts, obstructed = _formula_counts(expl)
    return {
        "bound_on_terms": bound,
        "rounds": plan.rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): sum(by_terms[n].values()) for n in sorted(by_terms)},
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": by_terms == _counted(sameness, bra, bound),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "rounds_agreeing_with_unbounded_formula": [
            expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)
        ],
        "same_results_rounds_and_attempts_as_second_derivation_without_identifications": (
            same_as_second(expl, second)
        ),
        "additions_never_negative": all(min(added(s)) >= 0 for s in expl.depth),
        "attempts_equal_formula_1_plus_n_squared_minus_m": expl.attempts_per_round[-1] == attempts,
        "obstructed_equal_formula_n": expl.obstructed_per_round[-1] == obstructed,
        "frontier_states": len(entries),
        "frontier_attempts": len({(leave.state, leave.change) for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": one_plus_two_n,
        "obstructed_attempts": check.obstructed,
        "answers_within_bound": check.answers_within,
        "answers_beyond_bound": check.answers_beyond,
        "answers_removing_the_obstruction": removal_answers(expl),
        "answers_reaching_something_new": list(check.failures),
        "changes_checked": edges.checked,
        "round_not_raised_by_one": list(edges.round_not_raised_by_one),
        "counts_lowered_by": list(edges.counts_lowered_by),
        "fewest_classes_lowered_by": list(edges.fewest_classes_lowered_by),
        "sequences_of_changes_total": sum(sequences.values()),
        "results_reached_by_one_sequence": sum(1 for c in sequences.values() if c == 1),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results by terms, completeness, cost formula.

    No per-result file is written; the frontier is counted, not exported.
    The second derivation's exploration without identifications is run at the
    same bound and compared.
    """
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    second = explore_second(start, bound, rounds, additions_only=True)
    by_terms = _by_terms(expl)
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    return {
        "bound_on_terms": bound,
        "results": len(expl.depth),
        "results_by_terms": {str(n): sum(by_terms[n].values()) for n in sorted(by_terms)},
        "last_round_with_a_new_result": expl.last_new_round,
        "changes_attempted": expl.attempts_per_round[-1],
        "of_which_obstructed": expl.obstructed_per_round[-1],
        "explored_equals_independent_count": by_terms == _counted(sameness, bra, bound),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "same_results_rounds_and_attempts_as_second_derivation_without_identifications": (
            same_as_second(expl, second)
        ),
        "frontier_states": len({leave.state for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
    }


def write_log(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> int:
    """The full attempt log of a small exploration (bound `plan.log_bound`)."""
    expl = explore(given(bra, sameness), plan.log_bound, plan.rounds, keep_log=True)
    path = out / f"attempts_bound{plan.log_bound}_{sameness.value}_{alternative(bra)}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in expl.log:
            line = attempt_record(rec, expl.depth[rec.state] + 1)
            handle.write(json.dumps(line, sort_keys=True, ensure_ascii=True) + "\n")
    return len(expl.log)


def write_reach(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> dict[str, object]:
    """`reach_bound{B}_{tag}.csv`: which result reaches which, by containment and by search.

    Every ordered pair is also tested with the second derivation's carrying
    map: what the third seed reaches the second reaches too, and the pairs
    the second reaches and the third does not are counted.
    """
    bound = plan.reach_bound
    expl = explore(given(bra, sameness), bound, plan.rounds)
    states = sorted(expl.depth, key=order)
    rows: list[list[object]] = []
    disagreements: list[str] = []
    ordered = mutual = under_second = second_only = third_only = 0
    for s in states:
        by_search = reachable_by_search(s, bound)
        if not by_search <= set(states):
            disagreements.append(f"{s.key()} -> a state that is not a result")
        for t in states:
            q = embedding(s, t)
            here = q is not None
            second = reachable_second(s, t)
            if here != (t in by_search):
                disagreements.append(f"{s.key()} -> {t.key()}")
            rows.append(
                [
                    s.key(),
                    t.key(),
                    int(here),
                    "" if q is None else " ".join(map(str, q)),
                    int(second),
                ]
            )
            ordered += here
            under_second += second
            second_only += second and not here
            third_only += here and not second
            if here and s != t and reachable(t, s):
                mutual += 1
    tag = f"{sameness.value}_{alternative(bra)}"
    _write_csv(
        out / f"reach_bound{bound}_{tag}.csv",
        ("from", "to", "reachable", "embedding", "reachable_under_second_seed"),
        rows,
    )
    return {
        "bound_on_terms": bound,
        "results": len(states),
        "ordered_pairs": len(rows),
        "ordered_pairs_reachable": ordered,
        "unordered_pairs_reachable_both_ways": mutual // 2,
        "ordered_pairs_reachable_under_second_seed": under_second,
        "pairs_reachable_under_second_seed_only": second_only,
        "pairs_reachable_here_but_not_under_second_seed": third_only,
        "embedding_agrees_with_search": not disagreements,
        "disagreements": disagreements,
    }


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    checked, cost_mismatches = check_free_cost(min(plan.free_bound, 4))
    summary: dict[str, object] = {
        "plan": {
            "bound_on_terms_free": plan.free_bound,
            "bound_on_terms_anchored": plan.anchored_bound,
            "bound_on_terms_anchored_census": plan.census_bound,
            "bound_on_terms_full_log": plan.log_bound,
            "bound_on_terms_reachability": plan.reach_bound,
            "rounds": plan.rounds,
            "unbounded_round_counts_upto": plan.layers_upto,
        },
        "given": write_given(out),
        "independent_counts": write_counts(out, plan),
        "free_cost_closed_form_checked_on": checked,
        "free_cost_closed_form_mismatches": cost_mismatches,
    }
    runs: dict[str, object] = {}
    reach: dict[str, object] = {}
    logged: dict[str, int] = {}
    census: dict[str, object] = {}
    for sameness in Sameness:
        for bra in (False, True):
            tag = f"{sameness.value}/{alternative(bra)}"
            runs[tag] = write_run(out, sameness, bra, plan)
            reach[tag] = write_reach(out, sameness, bra, plan)
            logged[tag] = write_log(out, sameness, bra, plan)
            if sameness is Sameness.ANCHORED and plan.census_bound > plan.anchored_bound:
                census[tag] = write_census(sameness, bra, plan.census_bound, plan.rounds)
    summary["runs"] = runs
    summary["reachability"] = reach
    summary["attempts_in_full_logs"] = logged
    summary["anchored_census"] = census
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
