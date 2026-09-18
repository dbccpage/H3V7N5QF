"""Writes `evidence/second/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_second.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest, `compare_evidence`,
    `states_on_given_terms`, `alternative`, `added_rows` and `frontier_rows`
    do not depend on the kinds of change.  `attempt_record`, `result_rows`,
    `write_given`, `write_run` and `write_counts` are written afresh because
    they list changes, answers, costs and counts.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

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
from xry.orbits import count_free, count_named
from xry.state import Sameness, State, added, canonical, given

from second.changes import (
    REMOVAL_IMPOSSIBLE,
    Answer,
    Kind,
    changes,
    is_build_of,
    obstruction,
    one_term_builds,
    perform,
)
from second.cost import cost, cost_free, cost_free_by_placement
from second.explore import check_answers, explore, removal_answers, rigid
from second.follows import verdicts
from second.invariants import fewest_classes
from second.orbits import count_results, layer_counts
from second.reach import carrying_map, reachable, reachable_by_search

__all__ = [
    "Plan",
    "attempt_record",
    "check_classes",
    "check_free_cost",
    "compare_evidence",
    "result_rows",
    "write_all",
    "write_census",
    "write_counts",
    "write_given",
    "write_log",
    "write_reach",
    "write_run",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    `census_bound` is a larger bound for the ANCHORED runs at which only
    counts are recorded (no per-result files); `0` turns the census off.
    """

    free_bound: int = 5
    anchored_bound: int = 4
    census_bound: int = 5
    log_bound: int = 3
    reach_bound: int = 3
    rounds: int = 100
    layers_upto: int = 20
    count_upto: int = 6

    def bound(self, sameness: Sameness) -> int:
        """The declared bound on the number of terms under `sameness`."""
        return self.free_bound if sameness is Sameness.FREE else self.anchored_bound


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
                if change.kind is Kind.ADD_ASSERTION and obstruction(start, change):
                    all_builds = one_term_builds(start, change.x)
                    not_builds += sum(1 for b in all_builds if not is_build_of(b, start, change))
                    distinct = sorted({canonical(b) for b in all_builds}, key=order)
                    builds[change.written(start)] = {
                        "one_term_builds": len(all_builds),
                        "up_to_sameness": [b.written() for b in distinct],
                    }
            one = State.of(1, [], None if sameness is Sameness.FREE else (0, 0))
            doc[f"{sameness.value}/{alternative(bra)}"] = {
                "state": start.written(),
                "attempts": [attempt_record(rec, 1) for rec in expl.log],
                "builds_with_one_added_term": builds,
                "reaches_the_other_beginning": reachable(start, given(not bra, sameness)),
                "reaches_the_one_term_state": reachable(start, one),
            }
    _write_json(out / "given.json", doc)
    return {"states_on_given_terms": len(found), "listed_builds_that_are_not_builds": not_builds}


def result_rows(expl: Exploration, bra: bool) -> list[list[object]]:
    """One row per result: additions, round, cost, fewest classes, obstructions, return."""
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        terms, assertions = added(state)
        tried = changes(state)
        blocked = [c for c in tried if obstruction(state, c)]
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
                len(tried),
                sum(1 for c in blocked if c.kind is Kind.IDENTIFY),
                sum(1 for c in blocked if c.kind is Kind.ADD_ASSERTION),
                int(rigid(state)),
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
    "obstructed_identifications",
    "obstructed_additions",
    "every_identification_obstructed",
    "reaches_what_is_given",
)


def check_classes(expl: Exploration) -> tuple[int, list[str]]:
    """Fewest classes never decrease along an unobstructed change within the bound.

    Returns how many changes were checked and the ones that lowered the number.
    """
    known: dict[State, int] = {}

    def classes(state: State) -> int:
        if state not in known:
            known[state] = fewest_classes(state)
        return known[state]

    checked = 0
    lowered: list[str] = []
    for state in sorted(expl.depth, key=order):
        before = classes(state)
        for change in changes(state):
            if obstruction(state, change):
                continue
            out = perform(state, change)
            if out.n > expl.bound:
                continue
            checked += 1
            if classes(canonical(out)) < before:
                lowered.append(f"{state.key()} / {change.written(state)}")
    return checked, lowered


def _by_terms(expl: Exploration) -> dict[int, dict[int, int]]:
    """Explored results by number of terms, then by number of assertions."""
    out: dict[int, dict[int, int]] = {}
    for state in expl.depth:
        by_m = out.setdefault(state.n, {})
        by_m[state.m] = by_m.get(state.m, 0) + 1
    return out


def _counted(sameness: Sameness, bra: bool, bound: int) -> dict[int, dict[int, int]]:
    """The independent count in the shape of `_by_terms` (zero rows left out)."""
    out = {}
    for n in range(1, bound + 1):
        per_m = {m: c for m, c in enumerate(count_results(sameness, bra, n)) if c}
        if per_m:
            out[n] = per_m
    return out


def write_run(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> dict[str, object]:
    """All files of one exploration; returns its summary."""
    tag = f"{sameness.value}_{alternative(bra)}"
    bound = plan.bound(sameness)
    start = given(bra, sameness)
    expl = explore(start, bound, plan.rounds)
    alone = explore(start, bound, plan.rounds, additions_only=True)

    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, bra))
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
                alone.new_per_round[r],
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
            "new_results_by_additions_alone",
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
    classes_checked, classes_lowered = check_classes(expl)
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
        "additions_alone_reach_the_same_results_in_the_same_rounds": alone.depth == expl.depth,
        "additions_never_negative": all(min(added(s)) >= 0 for s in expl.depth),
        "frontier_states": len(entries),
        "frontier_attempts": len({(leave.state, leave.change) for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": one_plus_two_n,
        "obstructed_attempts": check.obstructed,
        "answers_within_bound": check.answers_within,
        "answers_beyond_bound": check.answers_beyond,
        "answers_removing_the_obstruction": removal_answers(expl),
        "answers_reaching_something_new": list(check.failures),
        "fewest_classes_checked_on": classes_checked,
        "fewest_classes_lowered_by": classes_lowered,
        "every_identification_obstructed": sum(1 for s in expl.depth if rigid(s)),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results by terms, completeness, cost formula.

    No per-result file is written; the frontier is counted, not exported.
    """
    expl = explore(given(bra, sameness), bound, rounds)
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
    """`reach_bound{B}_{tag}.csv`: which result reaches which, by carrying map and by search."""
    bound = plan.reach_bound
    expl = explore(given(bra, sameness), bound, plan.rounds)
    states = sorted(expl.depth, key=order)
    rows: list[list[object]] = []
    disagreements: list[str] = []
    ordered = mutual = 0
    for s in states:
        by_search = reachable_by_search(s, bound)
        if not by_search <= set(states):
            disagreements.append(f"{s.key()} -> a state that is not a result")
        for t in states:
            q = carrying_map(s, t)
            if (q is not None) != (t in by_search):
                disagreements.append(f"{s.key()} -> {t.key()}")
            rows.append(
                [s.key(), t.key(), int(q is not None), "" if q is None else " ".join(map(str, q))]
            )
            if q is not None:
                ordered += 1
                if s != t and reachable(t, s):
                    mutual += 1
    tag = f"{sameness.value}_{alternative(bra)}"
    _write_csv(
        out / f"reach_bound{bound}_{tag}.csv", ("from", "to", "reachable", "carrying_map"), rows
    )
    return {
        "bound_on_terms": bound,
        "results": len(states),
        "ordered_pairs": len(rows),
        "ordered_pairs_reachable": ordered,
        "unordered_pairs_reachable_both_ways": mutual // 2,
        "carrying_map_agrees_with_search": not disagreements,
        "disagreements": disagreements,
    }


def write_counts(out: Path, plan: Plan) -> dict[str, list[int]]:
    """`counts.csv`: results by terms and assertions, by independent count, beside all legal states."""
    rows: list[list[object]] = []
    combos = [(s, b) for s in Sameness for b in (False, True)]
    totals: dict[str, list[int]] = {f"{s.value}/{alternative(b)}": [] for s, b in combos}
    for n in range(1, plan.count_upto + 1):
        columns = {f"{s.value}/{alternative(b)}": count_results(s, b, n) for s, b in combos}
        for key, counts in columns.items():
            totals[key].append(sum(counts))
        free = count_free(n)
        named = count_named(n)
        for m in range(n * (n - 1) + 1):
            rows.append(
                [
                    n,
                    m,
                    *(columns[key][m] for key in totals),
                    free[m],
                    sum(named[kind][m] for kind in named),
                ]
            )
    _write_csv(
        out / "counts.csv",
        (
            "terms",
            "assertions",
            *(f"results {key}" for key in totals),
            "all legal states free",
            "all legal states anchored",
        ),
        rows,
    )
    return totals


def check_free_cost(bound: int) -> tuple[int, list[str]]:
    """Compare the closed form for FREE cost with the best placement of names.

    Every legal state with at most `bound` terms is compared, results and
    non-results alike (both formulas say `None` for the latter).
    """
    checked = 0
    mismatches = []
    for bra in (False, True):
        for n in range(1, bound + 1):
            seen: set[State] = set()
            for mask in range(1 << (n * n)):
                state = State(n, mask)
                if not state.legal:
                    continue
                state = canonical(state)
                if state in seen:
                    continue
                seen.add(state)
                if cost_free(state, bra) != cost_free_by_placement(state, bra):
                    mismatches.append(f"{alternative(bra)}/{state.key()}")
                checked += 1
    return checked, mismatches


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
