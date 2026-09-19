"""Writes `evidence/fifth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_fifth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest, `compare_evidence` and
    `alternative` do not depend on which changes there are.

Cited from the fourth derivation (`fourth.explore`, `fourth.reach`,
`fourth.orbits`) and re-checked by computation
    The fourth derivation's exploration is run beside the fifth's at the same
    bound and rounds; the fifth's results with no destroyed given must be the
    fourth's results, at the same rounds, with the same numbers of shortest
    sequences (`compare_with_fourth`); the fourth's reachability (containment)
    must imply the fifth's on every pair of the fourth's results, and the
    pairs reachable now that were not then are counted (`write_reach`); the
    fourth's counts by terms and total multiplicity must be the lost = 0
    part of the fifth's (`write_counts`).  This is the computed form of rule
    5 for the fourth's computed claims.

Everything about the four kinds — the attempt records, the result rows, the
checks on changes, the counts by destroyed givens, the reachability by the
names criterion and by graph search — is written afresh.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from itertools import product
from math import comb
from pathlib import Path

from fourth.explore import Exploration as ExplorationFourth
from fourth.explore import count_sequences as count_sequences_fourth
from fourth.explore import explore as explore_fourth
from fourth.orbits import counts_upto as counts_upto_fourth
from fourth.reach import reachable as reachable_fourth
from fourth.state import given as given_fourth
from xry.evidence import _write_csv, _write_json, alternative, compare_evidence, write_manifest
from xry.state import Sameness

from fifth.changes import (
    REMOVAL_IS_REFUSAL,
    Answer,
    Change,
    Kind,
    attempt_counts,
    changes,
    is_build_of,
    obstruction,
    obstruction_counted,
    one_term_builds,
    perform,
)
from fifth.cost import cost, cost_free, cost_free_by_placement, lost, lost_free, raises_by_one
from fifth.explore import (
    Attempt,
    Exploration,
    check_answers,
    count_shortest_sequences,
    cycle,
    explore,
    order,
    performed,
    removal_answers,
    sequences_exact,
)
from fifth.follows import verdicts
from fifth.invariants import cost_rises_by_at_most_one, fewest_classes, lowered, names_stay_merged
from fifth.orbits import NAMED_KINDS, count_free_all, count_named, count_one_way, counts_by_lost, counts_upto, layer_counts
from fifth.reach import reach_graph, reachable, reachable_in_graph
from fifth.state import MState, added, canonical, forget_canonical_forms, given, names_one_term

__all__ = [
    "ChangeCheck",
    "Plan",
    "added_rows",
    "attempt_record",
    "check_changes",
    "check_free_cost",
    "compare_evidence",
    "compare_with_fourth",
    "destroyed",
    "frontier_rows",
    "result_rows",
    "two_term_round_count",
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

    Every exploration is bounded in terms and in rounds (the results within a
    bound on terms are infinite, as under the fourth seed).  Three
    explorations per beginning and reading: the main one (`free_bound` /
    `anchored_bound` terms, `rounds` rounds), a deeper one with fewer terms
    (`deep_bound`, `deep_rounds`), and one with the given terms only and all
    `two_term_rounds` rounds.  `census_bound` is a larger bound for the
    ANCHORED runs at which only counts are recorded; `0` turns the census
    off.  Reachability is tested among the results of (`reach_bound`,
    `reach_rounds`) along the changes among the results of (`reach_bound`,
    `reach_rounds + reach_extra`), enough rounds for every sequence the
    paper's proof uses.
    """

    free_bound: int = 5
    anchored_bound: int = 4
    rounds: int = 8
    census_bound: int = 5
    deep_bound: int = 3
    deep_rounds: int = 12
    two_term_rounds: int = 100
    log_bound: int = 2
    log_rounds: int = 4
    reach_bound: int = 3
    reach_rounds: int = 6
    reach_extra: int = 3
    layers_upto: int = 20
    count_upto: int = 5
    count_total_upto: int = 12

    def bound(self, sameness: Sameness) -> int:
        """The declared bound on the number of terms under `sameness`."""
        return self.free_bound if sameness is Sameness.FREE else self.anchored_bound

    def runs(self, sameness: Sameness) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the explorations written for `sameness`."""
        return ((self.bound(sameness), self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(sameness: Sameness, bra: bool, bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}_{sameness.value}_{alternative(bra)}"


def destroyed(state: MState, bra: bool) -> int:
    """The destroyed givens of a result under the sameness its names imply."""
    return lost_free(state, bra) if state.names is None else lost(state, bra)


def _further_written(state: MState, ans: Answer) -> list[str]:
    """The further changes of an answer, in words (an added term is written as in the result)."""
    return [c.written(ans.result if max(c.x, c.y) >= state.n else state) for c in ans.further]


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change, the obstruction (with multiplicities), the answers.

    For an obstructed addition of `xrx` the record also says what "remove the
    obstruction" comes to under this seed.
    """
    w = rec.state.term_writing()
    counted = obstruction_counted(rec.state, rec.change)
    return {
        "state": rec.state.key(),
        "written": rec.state.written(),
        "round": round_,
        "change": rec.change.written(rec.state),
        "kind": rec.change.kind.value,
        "adds": list(rec.change.additions),
        "changes_a_multiplicity_to": (
            None
            if rec.change.kind not in (Kind.ADD_ASSERTION, Kind.REMOVE)
            else rec.state.mult_of(rec.change.x, rec.change.y) + (1 if rec.change.kind is Kind.ADD_ASSERTION else -1)
        ),
        "obstruction": [f"{w[x]}r{w[y]}" + (f"({k})" if k > 1 else "") for x, y, k in counted],
        "outcome": None if rec.outcome is None else rec.outcome.key(),
        "beyond_bound": rec.beyond,
        "remove_the_obstruction": (
            REMOVAL_IS_REFUSAL if rec.obstruction and rec.change.kind is Kind.ADD_ASSERTION else None
        ),
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
    """`given.json`: the alternatives for what is given, every attempt on them, what they reach."""
    doc: dict[str, object] = {
        "legal_states_on_the_given_terms": "infinite: `arb` i times and `bra` j times for every i, j; the names one term with nothing asserted",
        "results_among_them": "all of them (every legal state with at least one term is a result)",
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
                elif obstruction(start, change):
                    not_builds += int(not is_build_of(start, start, change))
            one = MState.of(1, [], None if sameness is Sameness.FREE else (0, 0))
            twice = MState.of(2, [(0, 1), (0, 1)] + ([(1, 0)] if bra else []), start.names)
            empty = MState.of(2, [], start.names)
            attempts, obstructed = attempt_counts(start)
            doc[f"{sameness.value}/{alternative(bra)}"] = {
                "state": start.written(),
                "changes": attempts,
                "of_which_obstructed": obstructed,
                "attempts": [attempt_record(rec, 1) for rec in expl.log],
                "builds_with_one_added_term": builds,
                "reaches_the_other_beginning": reachable(start, given(not bra, sameness)),
                "the_other_beginning_reaches_it": reachable(given(not bra, sameness), start),
                "reaches_the_one_term_state": reachable(start, one),
                "the_one_term_state_reaches_it": reachable(one, start),
                "reaches_arb_asserted_twice": reachable(start, twice),
                "arb_asserted_twice_reaches_what_is_given": reachable(twice, start),
                "reaches_nothing_asserted": reachable(start, empty),
                "nothing_asserted_reaches_what_is_given": reachable(empty, start),
                "cost_of_nothing_asserted": cost(empty, bra),
                "cost_of_the_one_term_state": cost(one, bra),
            }
    _write_json(out / "given.json", doc)
    return {"listed_builds_that_are_not_builds": not_builds}


def result_rows(expl: Exploration, bra: bool, sequences: dict[MState, int]) -> list[list[object]]:
    """One row per result."""
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
                state.distinct,
                state.most,
                terms,
                assertions,
                expl.depth[state],
                "" if c is None else c,
                destroyed(state, bra),
                fewest_classes(state),
                attempts,
                obstructed - state.n,
                state.n,
                int(expl.depth[state] < expl.rounds),
                sequences[state],
                int(sequences_exact(expl, state)),
                int(reachable(state, expl.start)),
                int(names_one_term(state)),
                int(destroyed(state, bra) == 0),
                int(state.simple),
            ]
        )
    return rows


RESULT_HEADER = (
    "state",
    "written",
    "terms",
    "assertions_counted",
    "assertions_asserted",
    "largest_multiplicity",
    "terms_added_to_given",
    "assertions_added_to_given",
    "round_first_reached",
    "fewest_changes_by_formula",
    "destroyed_givens",
    "fewest_classes",
    "changes",
    "obstructed_identifications",
    "obstructed_additions",
    "changes_attempted",
    "shortest_sequences_of_changes",
    "shortest_sequences_exact_within_bound",
    "reaches_what_is_given",
    "names_one_term",
    "contains_what_is_given",
    "asserts_nothing_twice",
)


def added_rows(expl: Exploration) -> list[list[int]]:
    """Results grouped by (terms added, assertions added), fewest additions first."""
    groups: dict[tuple[int, int], list[int]] = {}
    for state, round_ in expl.depth.items():
        groups.setdefault(added(state), []).append(round_)
    ordered = sorted(groups, key=lambda k: (max(k[0], 0) + max(k[1], 0), k))
    return [[t, a, len(groups[t, a]), min(groups[t, a]), max(groups[t, a])] for t, a in ordered]


def frontier_rows(expl: Exploration) -> list[list[object]]:
    """One row per frontier state, with how many of its attempts leave the bound on terms."""
    per_state: dict[MState, dict[str, int]] = {}
    for leave in expl.frontier:
        ways = per_state.setdefault(leave.state, {})
        ways[leave.by] = ways.get(leave.by, 0) + 1
    return [
        [
            state.key(),
            state.written(),
            expl.depth[state],
            per_state[state].get("the change", 0),
            per_state[state].get("build structure", 0),
        ]
        for state in sorted(per_state, key=order)
    ]


@dataclass(frozen=True)
class ChangeCheck:
    """What `check_changes` found on every unobstructed change within the bound."""

    checked: int
    cost_raised_by_more_than_one: tuple[str, ...]
    cost_rule_disagreements: tuple[str, ...]
    names_told_apart_again: tuple[str, ...]
    lowering: dict[str, int]
    round_raised: int
    round_kept: int
    round_lowered: int


def check_changes(expl: Exploration, bra: bool) -> ChangeCheck:
    """On every unobstructed change within the bound: the cost rises by at most one, and more.

    Checks that the outcome's cost is at most the state's plus one; with
    names, that the rule saying which changes raise it by exactly one agrees
    with the outcome; that names once one term stay one term; and counts the
    changes on which the fourth's never-decreasing counts decrease and the
    changes whose outcome is of a lower, the same, or the next round.
    """
    checked = 0
    over: list[str] = []
    wrong: list[str] = []
    apart: list[str] = []
    lowering: dict[str, int] = {}
    raised = kept = fell = 0
    for state, change, out in performed(expl):
        checked += 1
        name = f"{state.key()} / {change.written(state)}"
        raw = perform(state, change)
        if not cost_rises_by_at_most_one(state, raw, bra):
            over.append(name)
        if state.names is not None and raises_by_one(state, change, bra) != (cost(raw, bra) == (cost(state, bra) or 0) + 1):
            wrong.append(name)
        if not names_stay_merged(state, raw):
            apart.append(name)
        for what in lowered(state, raw):
            lowering[what] = lowering.get(what, 0) + 1
        step = expl.depth[out] - expl.depth[state]
        if step > 0:
            raised += 1
        elif step == 0:
            kept += 1
        else:
            fell += 1
    return ChangeCheck(checked, tuple(over), tuple(wrong), tuple(apart), dict(sorted(lowering.items())), raised, kept, fell)


def compare_with_fourth(expl: Exploration, fourth: ExplorationFourth, sequences: dict[MState, int], bra: bool) -> dict[str, object]:
    """The results with no destroyed given against the fourth derivation's exploration.

    Both explorations must have the same bound on terms and the same rounds.
    The results with no destroyed given, with their rounds, must be exactly
    the fourth's results with their rounds, and the number of shortest
    sequences reaching each must be the fourth's number of sequences.
    """
    kept = {s: r for s, r in expl.depth.items() if destroyed(s, bra) == 0}
    rounds_agree = kept == fourth.depth
    fourth_sequences = count_sequences_fourth(fourth)
    sequences_agree = rounds_agree and all(sequences[s] == fourth_sequences[s] for s in kept)
    return {
        "results_containing_what_is_given": len(kept),
        "fourth_derivation_results": len(fourth.depth),
        "same_results_and_rounds_as_fourth_derivation": rounds_agree,
        "same_shortest_sequence_counts_as_fourth_derivation": sequences_agree,
    }


def _by_lost(expl: Exploration, bra: bool) -> dict[str, int]:
    """Explored results by (terms, total multiplicity, destroyed givens), as text keys."""
    out: dict[str, int] = {}
    for state in expl.depth:
        key = f"{state.n}/{state.m}/{destroyed(state, bra)}"
        out[key] = out.get(key, 0) + 1
    return out


def _counted(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, int]:
    """The independent count in the shape of `_by_lost`, restricted to cost within `rounds`."""
    size0 = 2 + (2 if bra else 1)
    out: dict[str, int] = {}
    for n in range(1, bound + 1):
        for value, counts in counts_by_lost(sameness, bra, n, size0 + rounds).items():
            for t, c in enumerate(counts):
                if c and n + t - size0 + 2 * value <= rounds:
                    out[f"{n}/{t}/{value}"] = c
    return out


def two_term_round_count(bra: bool, r: int) -> int:
    """Results of round `r` with at most the given terms, names kept, in closed form.

    Without `bra`: `arb` `1 + i` times and `bra` `j` times with `i + j = r`
    (`r + 1`); `arb` missing and `bra` `r − 1` times (one, `r ≥ 1`); the
    one-term state (round 2); `a = b` with a second term and `r − 3` units of
    multiplicity between them (`r − 2`, `r ≥ 3`).  With `bra`: both at least
    once with `i + j = r + 2` (`r + 1`); one of them missing (two, `r ≥ 1`);
    nothing asserted (round 2); the one-term state (round 3); `a = b` with a
    second term (`r − 3`, `r ≥ 4`).
    """
    if not bra:
        return (r + 1) + (1 if r >= 1 else 0) + (1 if r == 2 else 0) + max(r - 2, 0)
    return (r + 1) + (2 if r >= 1 else 0) + (1 if r == 2 else 0) + (1 if r == 3 else 0) + max(r - 3, 0)


def _two_term_binomial(expl: Exploration, sequences: dict[MState, int], bra: bool) -> bool | None:
    """On two-term results with names and no destroyed given: sequences = C(i + j, i)."""
    if expl.start.names is None:
        return None
    a0, b0 = expl.start.names
    given_bra = expl.start.mult_of(b0, a0)
    for state in expl.depth:
        if state.n != 2 or state.names is None or destroyed(state, bra) != 0:
            continue
        a, b = state.names
        i, j = state.mult_of(a, b) - 1, state.mult_of(b, a) - given_bra
        if sequences[state] != comb(i + j, i):
            return False
    return True


def write_run(out: Path, sameness: Sameness, bra: bool, bound: int, rounds: int, plan: Plan) -> dict[str, object]:
    """All files of one exploration (`bound` terms, `rounds` rounds); returns its summary."""
    tag = run_tag(sameness, bra, bound, rounds)
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    fourth = explore_fourth(given_fourth(bra, sameness), bound, rounds)
    sequences = count_shortest_sequences(expl)

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

    exact = layer_counts(sameness, bra, min(plan.layers_upto, rounds))
    contained_per_round = [0] * (rounds + 1)
    merged_per_round = [0] * (rounds + 1)
    for state, r in expl.depth.items():
        contained_per_round[r] += destroyed(state, bra) == 0
        merged_per_round[r] += names_one_term(state)
    so_far = 0
    round_rows: list[list[object]] = []
    for r in range(rounds + 1):
        so_far += expl.new_per_round[r]
        round_rows.append(
            [
                r,
                expl.new_per_round[r],
                so_far,
                expl.attempts_per_round[r],
                expl.obstructed_per_round[r],
                contained_per_round[r],
                fourth.new_per_round[r],
                merged_per_round[r],
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
            "new_results_containing_what_is_given",
            "new_results_fourth_derivation",
            "new_results_with_the_names_one_term",
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

    by_terms: dict[int, int] = {}
    by_lost: dict[int, int] = {}
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
        by_lost[destroyed(state, bra)] = by_lost.get(destroyed(state, bra), 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    # Rounds 0 .. N - 2 are complete within the bound on terms; only rounds that were run can be compared.
    within_bound_layers = min(len(exact) - 1, bound - 2, rounds)
    check = check_answers(expl)
    entries: dict[MState, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s, r in expl.depth.items() if s.n == bound and r < rounds}
    one_plus_two_n = set(entries) == full and all(c == 1 + 2 * s.n for s, c in entries.items())
    edges = check_changes(expl, bra)
    tried = [s for s, r in expl.depth.items() if r < rounds]
    awaiting = expl.awaiting
    two_term_closed = (
        expl.new_per_round == [two_term_round_count(bra, r) for r in range(rounds + 1)]
        if bound == 2 and sameness is Sameness.ANCHORED
        else None
    )
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_by_destroyed_givens": {str(k): by_lost[k] for k in sorted(by_lost)},
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": _by_lost(expl, bra) == _counted(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "rounds_agreeing_with_unbounded_formula": [
            expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)
        ],
        "two_term_rounds_equal_closed_form": two_term_closed,
        **compare_with_fourth(expl, fourth, sequences, bra),
        "results_with_fewer_terms_or_assertions_than_given": sum(1 for s in expl.depth if min(added(s)) < 0),
        "results_with_the_names_one_term": sum(merged_per_round),
        "attempts_equal_formula": expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried),
        "obstructed_equal_formula": expl.obstructed_per_round[-1] == sum(attempt_counts(s)[1] for s in tried),
        "frontier_states": len(entries),
        "frontier_attempts": len({(leave.state, leave.change) for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": one_plus_two_n,
        "results_of_the_last_round_whose_changes_await": len(awaiting),
        "changes_awaiting": sum(attempt_counts(s)[0] for s in awaiting),
        "obstructed_attempts": check.obstructed,
        "answers_within_bound": check.answers_within,
        "answers_beyond_bound": check.answers_beyond,
        "answers_removing_the_obstruction": removal_answers(expl),
        "answers_reaching_something_new": list(check.failures),
        "changes_checked": edges.checked,
        "cost_raised_by_more_than_one": list(edges.cost_raised_by_more_than_one),
        "cost_rule_disagreements": list(edges.cost_rule_disagreements),
        "names_told_apart_again": list(edges.names_told_apart_again),
        "changes_lowering": edges.lowering,
        "changes_raising_the_round": edges.round_raised,
        "changes_keeping_the_round": edges.round_kept,
        "changes_lowering_the_round": edges.round_lowered,
        "results_with_a_two_change_cycle": sum(1 for s in expl.depth if cycle(s) is not None),
        "shortest_sequences_total": sum(sequences.values()),
        "results_reached_by_one_shortest_sequence": sum(1 for c in sequences.values() if c == 1),
        "results_with_exact_sequence_count": sum(1 for s in expl.depth if sequences_exact(expl, s)),
        "two_term_sequences_equal_binomial": _two_term_binomial(expl, sequences, bra),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results, completeness, cost formula, the fourth's.

    No per-result file is written; the frontier is counted, not exported.
    """
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    fourth = explore_fourth(given_fourth(bra, sameness), bound, rounds)
    sequences = count_shortest_sequences(expl)
    by_terms: dict[int, int] = {}
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "last_round_with_a_new_result": expl.last_new_round,
        "changes_attempted": expl.attempts_per_round[-1],
        "of_which_obstructed": expl.obstructed_per_round[-1],
        "explored_equals_independent_count": _by_lost(expl, bra) == _counted(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        **compare_with_fourth(expl, fourth, sequences, bra),
        "frontier_states": len({leave.state for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
        "results_of_the_last_round_whose_changes_await": len(expl.awaiting),
    }


def write_log(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> int:
    """The full attempt log of a small exploration (`plan.log_bound` terms, `plan.log_rounds` rounds)."""
    expl = explore(given(bra, sameness), plan.log_bound, plan.log_rounds, keep_log=True)
    tag = run_tag(sameness, bra, plan.log_bound, plan.log_rounds)
    path = out / f"attempts_{tag}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in expl.log:
            line = attempt_record(rec, expl.depth[rec.state] + 1)
            handle.write(json.dumps(line, sort_keys=True, ensure_ascii=True) + "\n")
    return len(expl.log)


def write_reach(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> dict[str, object]:
    """`reach_{tag}.csv`: what each result reaches, by the names criterion and by search.

    The results are those of (`reach_bound`, `reach_rounds`); the search
    follows the changes among the results of (`reach_bound`, `reach_rounds +
    reach_extra`), enough for every sequence the paper's proof of the
    criterion uses.  Every ordered pair is tested both ways; the file has
    one row per result with the counts, and the totals are in the summary,
    with the comparison with the fourth derivation's containment on the
    fourth's results.
    """
    bound, rounds = plan.reach_bound, plan.reach_rounds
    expl = explore(given(bra, sameness), bound, rounds)
    fourth = explore_fourth(given_fourth(bra, sameness), bound, rounds)
    wide = explore(given(bra, sameness), bound, rounds + plan.reach_extra)
    graph = reach_graph(wide)
    states = sorted(expl.depth, key=lambda s: (expl.depth[s], order(s)))
    inside = set(states)
    disagreements: list[str] = []
    reached_by: dict[MState, int] = {s: 0 for s in states}
    reaches: dict[MState, int] = {}
    found_counts: dict[MState, int] = {}
    ordered = mutual = 0
    fourth_pairs = fourth_reachable = fifth_on_fourth = fourth_not_fifth = 0
    fourth_among: dict[MState, int] = {}
    for s in states:
        found = reachable_in_graph(graph, s) & inside
        found_counts[s] = len(found)
        here_count = 0
        for t in states:
            here = reachable(s, t)
            if here != (t in found):
                disagreements.append(f"{s.key()} -> {t.key()}")
            here_count += here
            reached_by[t] += here
            if here and reachable(t, s):
                mutual += 1
            if s in fourth.depth and t in fourth.depth:
                fourth_pairs += 1
                before = reachable_fourth(s, t)
                fourth_reachable += before
                fifth_on_fourth += here
                fourth_not_fifth += before and not here
                fourth_among[s] = fourth_among.get(s, 0) + before
        reaches[s] = here_count
        ordered += here_count
    rows: list[list[object]] = [
        [
            s.key(),
            s.written(),
            expl.depth[s],
            int(names_one_term(s)),
            reaches[s],
            reached_by[s],
            found_counts[s],
            int(reaches[s] == found_counts[s]),
            int(reachable(s, expl.start)),
            int(s in fourth.depth),
            fourth_among.get(s, ""),
        ]
        for s in states
    ]
    tag = run_tag(sameness, bra, bound, rounds)
    _write_csv(
        out / f"reach_{tag}.csv",
        (
            "state",
            "written",
            "round",
            "names_one_term",
            "results_it_reaches",
            "results_reaching_it",
            "results_it_reaches_by_search",
            "criterion_agrees_with_search",
            "reaches_what_is_given",
            "is_a_result_of_the_fourth_seed",
            "fourth_results_it_reached_under_the_fourth_seed",
        ),
        rows,
    )
    pairs = len(states) * len(states)
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "search_rounds": rounds + plan.reach_extra,
        "results": len(states),
        "results_in_the_search": len(graph),
        "ordered_pairs": pairs,
        "ordered_pairs_reachable": ordered,
        "unordered_pairs_reachable_both_ways": (mutual - len(states)) // 2,
        "ordered_pairs_unreachable": pairs - ordered,
        "results_with_the_names_one_term": sum(1 for s in states if names_one_term(s)),
        "criterion_agrees_with_search": not disagreements,
        "disagreements": disagreements,
        "fourth_results": len(fourth.depth),
        "ordered_pairs_of_fourth_results": fourth_pairs,
        "of_which_reachable_under_the_fourth_seed": fourth_reachable,
        "of_which_reachable_under_the_fifth_seed": fifth_on_fourth,
        "reachable_under_the_fourth_seed_but_not_the_fifth": fourth_not_fifth,
        "fourth_reachability_implies_fifth": fourth_not_fifth == 0,
        "results_that_reach_what_is_given": sum(1 for s in states if reachable(s, expl.start)),
    }


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and total multiplicity, by independent count.

    All results (every legal state) under each reading, split by how the
    named terms stand and by the one-way property, beside the fourth
    derivation's counts of states containing what is given, which must be
    the lost = 0 part.
    """
    rows: list[list[object]] = []
    totals: dict[str, list[int]] = {"free": [], "anchored": []}
    fourth_is_lost_zero = True
    combos = [(s, b) for s in Sameness for b in (False, True)]
    for n in range(1, plan.count_upto + 1):
        degree = plan.count_total_upto
        free_all = count_free_all(n, degree)
        one_way = count_one_way(n, degree)
        named = count_named(n, degree)
        totals["free"].append(sum(free_all))
        totals["anchored"].append(sum(sum(v) for v in named.values()))
        fourth_counts = {f"{s.value}/{alternative(b)}": counts_upto_fourth(s, b, n, degree) for s, b in combos}
        ours_zero = {
            key: counts_by_lost(s, b, n, degree).get(0, [0] * (degree + 1)) for key, (s, b) in zip(fourth_counts, combos)
        }
        fourth_is_lost_zero = fourth_is_lost_zero and all(ours_zero[k] == fourth_counts[k] for k in fourth_counts)
        for t in range(degree + 1):
            rows.append(
                [
                    n,
                    t,
                    free_all[t],
                    one_way[t],
                    *(named[kind][t] for kind in NAMED_KINDS),
                    *(fourth_counts[key][t] for key in fourth_counts),
                ]
            )
    _write_csv(
        out / "counts.csv",
        (
            "terms",
            "total_multiplicity",
            "results free",
            "results free never both ways",
            *(f"results anchored: {k}" for k in NAMED_KINDS),
            *(f"fourth seed results {key}" for key in (f"{s.value}/{alternative(b)}" for s, b in combos)),
        ),
        rows,
    )
    return {"totals": totals, "fourth_counts_are_the_lost_zero_part": fourth_is_lost_zero}


def check_free_cost(bound: int, most: int) -> tuple[int, list[str]]:
    """Compare the closed form for FREE cost with the best placement of names.

    Every legal state with at most `bound` terms and no multiplicity above
    `most` is compared.
    """
    checked = 0
    mismatches = []
    for bra in (False, True):
        for n in range(1, bound + 1):
            seen: set[MState] = set()
            for mult in product(range(most + 1), repeat=n * n):
                state = MState(n, mult)
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
    checked, cost_mismatches = check_free_cost(min(plan.free_bound, 3), 2)
    summary: dict[str, object] = {
        "plan": {
            "bound_on_terms_free": plan.free_bound,
            "bound_on_terms_anchored": plan.anchored_bound,
            "rounds": plan.rounds,
            "bound_on_terms_anchored_census": plan.census_bound,
            "deep_run_bound_on_terms": plan.deep_bound,
            "deep_run_rounds": plan.deep_rounds,
            "two_term_run_rounds": plan.two_term_rounds,
            "full_log_bound_on_terms": plan.log_bound,
            "full_log_rounds": plan.log_rounds,
            "reachability_bound_on_terms": plan.reach_bound,
            "reachability_rounds": plan.reach_rounds,
            "reachability_search_rounds": plan.reach_rounds + plan.reach_extra,
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
            for bound, rounds in plan.runs(sameness):
                runs[f"{tag}/bound{bound}_rounds{rounds}"] = write_run(out, sameness, bra, bound, rounds, plan)
                forget_canonical_forms()
            reach[tag] = write_reach(out, sameness, bra, plan)
            logged[tag] = write_log(out, sameness, bra, plan)
            if sameness is Sameness.ANCHORED and plan.census_bound > plan.anchored_bound:
                census[tag] = write_census(sameness, bra, plan.census_bound, plan.rounds)
                forget_canonical_forms()
    summary["runs"] = runs
    summary["reachability"] = reach
    summary["attempts_in_full_logs"] = logged
    summary["anchored_census"] = census
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
