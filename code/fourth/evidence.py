"""Writes `evidence/fourth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_fourth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest, `compare_evidence`, `alternative`
    and `states_on_given_terms` do not depend on how assertions are counted
    (`states_on_given_terms` lists the states on the given terms asserting
    nothing twice, which is what it always listed).

Cited from the third derivation (`third.explore`, `third.reach`) and
re-checked by computation
    The third derivation's exploration is run beside the fourth's at the same
    bound and rounds, and the fourth's results asserting nothing twice, their
    rounds and their sequence counts must be the third's (`compare_with_third`);
    the third's reachability is compared pair by pair on those results
    (`write_reach`).  This is the computed form of rule 5 for the third's
    computed claims.

Everything that lists counted states — the attempt records, the result
rows, the frontier and added-rows tables, the checks on changes, the
independent counts and the FREE cost check — is written afresh.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from itertools import product
from math import comb
from pathlib import Path

from third.explore import count_sequences as count_sequences_third
from third.explore import explore as explore_third
from third.reach import reachable as reachable_third
from xry.evidence import (
    _write_csv,
    _write_json,
    alternative,
    compare_evidence,
    states_on_given_terms,
    write_manifest,
)
from xry.explore import Exploration as ExplorationThird
from xry.state import Sameness
from xry.state import canonical as canonical_third
from xry.state import given as given_third

from fourth.changes import (
    REMOVAL_IMPOSSIBLE,
    Answer,
    Change,
    Kind,
    attempt_counts,
    changes,
    is_build_of,
    obstruction,
    one_term_builds,
    perform,
)
from fourth.cost import cost, cost_free, cost_free_by_placement
from fourth.explore import (
    Attempt,
    Exploration,
    check_answers,
    count_sequences,
    explore,
    order,
    performed,
    removal_answers,
)
from fourth.follows import verdicts
from fourth.invariants import fewest_classes, never_decreases
from fourth.orbits import count_simple, counts_upto, layer_counts
from fourth.reach import embedding, reachable, reachable_by_search
from fourth.state import MState, added, canonical, given, support

__all__ = [
    "ChangeCheck",
    "Plan",
    "added_rows",
    "attempt_record",
    "check_changes",
    "check_free_cost",
    "compare_evidence",
    "compare_with_third",
    "frontier_rows",
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

    The results within any bound on terms are infinite, so every exploration
    is bounded in terms and in rounds.  Three explorations per beginning and
    reading: the main one (`free_bound` / `anchored_bound` terms, `rounds`
    rounds), a deeper one with fewer terms (`deep_bound`, `deep_rounds`), and
    one with the given terms only and all `two_term_rounds` rounds — the only
    setting in which the seed's 100 rounds complete.  `census_bound` is a
    larger bound for the ANCHORED runs at which only counts are recorded; `0`
    turns the census off.
    """

    free_bound: int = 5
    anchored_bound: int = 4
    rounds: int = 8
    census_bound: int = 5
    deep_bound: int = 3
    deep_rounds: int = 12
    two_term_rounds: int = 100
    log_bound: int = 2
    log_rounds: int = 6
    reach_bound: int = 3
    reach_rounds: int = 6
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


def _further_written(state: MState, ans: Answer) -> list[str]:
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
        "raises_a_multiplicity_to": (
            None
            if rec.change.kind is not Kind.ADD_ASSERTION
            else rec.state.mult_of(rec.change.x, rec.change.y) + 1
        ),
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


def _states_on_given_terms_upto(most: int) -> list[MState]:
    """Every legal state on `a`, `b` with `arb` asserted and no multiplicity above `most`."""
    out = []
    for i in range(1, most + 1):
        for j in range(most + 1):
            out.append(MState.of(2, [(0, 1)] * i + [(1, 0)] * j, (0, 1)))
    return out


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the alternatives for what is given, and every attempt on them."""
    simple = states_on_given_terms()
    most = 3
    upto = _states_on_given_terms_upto(most)
    doc: dict[str, object] = {
        "legal_states_on_the_given_terms_with_arb_asserting_nothing_twice": [s.written() for s in simple],
        "count_asserting_nothing_twice": len(simple),
        f"count_with_no_multiplicity_above_{most}": len(upto),
        "formula_for_no_multiplicity_above_K": "K * (K + 1)",
        "count_without_a_bound_on_multiplicity": "infinite",
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
            one = MState.of(1, [], None if sameness is Sameness.FREE else (0, 0))
            twice = MState.of(2, [(0, 1), (0, 1)] + ([(1, 0)] if bra else []), start.names)
            attempts, obstructed = attempt_counts(start)
            doc[f"{sameness.value}/{alternative(bra)}"] = {
                "state": start.written(),
                "changes": attempts,
                "of_which_obstructed": obstructed,
                "attempts": [attempt_record(rec, 1) for rec in expl.log],
                "builds_with_one_added_term": builds,
                "reaches_the_other_beginning": reachable(start, given(not bra, sameness)),
                "reaches_the_one_term_state": reachable(start, one),
                "reaches_arb_asserted_twice": reachable(start, twice),
                "arb_asserted_twice_reaches_what_is_given": reachable(twice, start),
            }
    _write_json(out / "given.json", doc)
    return {
        "states_on_given_terms_asserting_nothing_twice": len(simple),
        f"states_on_given_terms_with_no_multiplicity_above_{most}": len(upto),
        "listed_builds_that_are_not_builds": not_builds,
    }


def result_rows(expl: Exploration, bra: bool, sequences: dict[MState, int]) -> list[list[object]]:
    """One row per result: counts, additions, round, cost, classes, attempts, sequences, return."""
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
                fewest_classes(state),
                attempts,
                obstructed,
                int(expl.depth[state] < expl.rounds),
                sequences[state],
                int(reachable(state, expl.start)),
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
    "fewest_classes",
    "changes",
    "obstructed_additions",
    "changes_attempted",
    "sequences_of_changes",
    "reaches_what_is_given",
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
    round_not_raised_by_one: tuple[str, ...]
    counts_lowered_by: tuple[str, ...]
    fewest_classes_lowered_by: tuple[str, ...]


def check_changes(expl: Exploration) -> ChangeCheck:
    """On every unobstructed change within the bound: the round rises by one, no count falls.

    Checks that the outcome's round is the state's plus one, that terms and
    every multiplicity do not decrease while the size rises by one, and that
    the fewest classes do not decrease.
    """
    known: dict[MState, int] = {}

    def classes(state: MState) -> int:
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
        # The counts are compared on the outcome as performed, before it is rewritten.
        if not never_decreases(state, perform(state, change)):
            lowered.append(name)
        if classes(out) < classes(state):
            classes_lowered.append(name)
    return ChangeCheck(checked, tuple(round_off), tuple(lowered), tuple(classes_lowered))


def compare_with_third(
    expl: Exploration, third: ExplorationThird, sequences: dict[MState, int]
) -> dict[str, object]:
    """The results asserting nothing twice against the third derivation's exploration.

    Both explorations must have the same bound on terms and the same rounds.
    The supports of the results asserting nothing twice, with their rounds,
    must be exactly the third's results with their rounds, and the number of
    sequences reaching each must agree.
    """
    simple = {canonical_third(support(s)): s for s in expl.depth if s.simple}
    rounds_agree = {t: expl.depth[s] for t, s in simple.items()} == third.depth
    third_sequences = count_sequences_third(third)
    sequences_agree = rounds_agree and all(
        sequences[s] == third_sequences[t] for t, s in simple.items()
    )
    return {
        "results_asserting_nothing_twice": len(simple),
        "third_derivation_results": len(third.depth),
        "same_results_and_rounds_as_third_derivation": rounds_agree,
        "same_sequence_counts_as_third_derivation": sequences_agree,
    }


def _by_terms(expl: Exploration) -> dict[int, dict[int, int]]:
    """Explored results by number of terms, then by total multiplicity."""
    out: dict[int, dict[int, int]] = {}
    for state in expl.depth:
        by_t = out.setdefault(state.n, {})
        by_t[state.m] = by_t.get(state.m, 0) + 1
    return out


def _counted(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[int, dict[int, int]]:
    """The independent count in the shape of `_by_terms` (zero rows left out)."""
    size0 = 2 + (2 if bra else 1)
    out = {}
    for n in range(1, bound + 1):
        degree = size0 + rounds - n
        if degree < 0:
            continue
        per_t = {
            t: c for t, c in enumerate(counts_upto(sameness, bra, n, degree)) if c and n + t - size0 <= rounds
        }
        if per_t:
            out[n] = per_t
    return out


def _two_term_binomial(expl: Exploration, sequences: dict[MState, int]) -> bool | None:
    """On results with two terms and names: sequences = C(i + j, i), `arb` `1 + i` times, `bra` `j` times."""
    if expl.start.names is None:
        return None
    a0, b0 = expl.start.names
    given_bra = expl.start.mult_of(b0, a0)
    for state in expl.depth:
        if state.n != 2 or state.names is None:
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
    third = explore_third(given_third(bra, sameness), bound, rounds)
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

    exact = layer_counts(sameness, bra, min(plan.layers_upto, rounds))
    simple_per_round = [0] * (rounds + 1)
    for state, r in expl.depth.items():
        simple_per_round[r] += state.simple
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
                simple_per_round[r],
                third.new_per_round[r],
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
            "new_results_asserting_nothing_twice",
            "new_results_third_derivation",
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
    # Rounds 0 .. N - 2 are complete within the bound on terms; only rounds that were run can be compared.
    within_bound_layers = min(len(exact) - 1, bound - 2, rounds)
    check = check_answers(expl)
    entries: dict[MState, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s, r in expl.depth.items() if s.n == bound and r < rounds}
    one_plus_two_n = set(entries) == full and all(c == 1 + 2 * s.n for s, c in entries.items())
    edges = check_changes(expl)
    tried = [s for s, r in expl.depth.items() if r < rounds]
    awaiting = expl.awaiting
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): sum(by_terms[n].values()) for n in sorted(by_terms)},
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": by_terms == _counted(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "rounds_agreeing_with_unbounded_formula": [
            expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)
        ],
        **compare_with_third(expl, third, sequences),
        "additions_never_negative": all(min(added(s)) >= 0 for s in expl.depth),
        "attempts_equal_formula_1_plus_n_squared": (
            expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried)
        ),
        "obstructed_equal_formula_n": expl.obstructed_per_round[-1] == sum(attempt_counts(s)[1] for s in tried),
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
        "round_not_raised_by_one": list(edges.round_not_raised_by_one),
        "counts_lowered_by": list(edges.counts_lowered_by),
        "fewest_classes_lowered_by": list(edges.fewest_classes_lowered_by),
        "sequences_of_changes_total": sum(sequences.values()),
        "results_reached_by_one_sequence": sum(1 for c in sequences.values() if c == 1),
        "two_term_sequences_equal_binomial": _two_term_binomial(expl, sequences),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results by terms, completeness, cost formula, the third's.

    No per-result file is written; the frontier is counted, not exported.
    """
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    third = explore_third(given_third(bra, sameness), bound, rounds)
    sequences = count_sequences(expl)
    by_terms = _by_terms(expl)
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): sum(by_terms[n].values()) for n in sorted(by_terms)},
        "last_round_with_a_new_result": expl.last_new_round,
        "changes_attempted": expl.attempts_per_round[-1],
        "of_which_obstructed": expl.obstructed_per_round[-1],
        "explored_equals_independent_count": by_terms == _counted(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        **compare_with_third(expl, third, sequences),
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
    """`reach_{tag}.csv`: which result reaches which, by containment and by search.

    Every ordered pair of results is tested both ways and the totals are in
    the summary; the file lists the pairs that carry information: every
    reachable pair with its embedding, and every pair of results asserting
    nothing twice, reachable or not, with the third derivation's verdict on
    it (which must agree).  An ordered pair of results absent from the file
    is unreachable and has a multiplicity above one on at least one side.
    """
    bound, rounds = plan.reach_bound, plan.reach_rounds
    expl = explore(given(bra, sameness), bound, rounds)
    states = sorted(expl.depth, key=order)
    rows: list[list[object]] = []
    disagreements: list[str] = []
    third_disagreements: list[str] = []
    ordered = mutual = simple_pairs = simple_reachable = counted_only = pairs = 0
    for s in states:
        by_search = reachable_by_search(s, bound, rounds - expl.depth[s])
        if not by_search <= set(states):
            disagreements.append(f"{s.key()} -> a state that is not a result")
        for t in states:
            pairs += 1
            q = embedding(s, t)
            here = q is not None
            both_simple = s.simple and t.simple
            third: bool | None = None
            if both_simple:
                simple_pairs += 1
                simple_reachable += here
                third = reachable_third(canonical_third(support(s)), canonical_third(support(t)))
                if third != here:
                    third_disagreements.append(f"{s.key()} -> {t.key()}")
            elif here:
                counted_only += 1
            if here != (t in by_search):
                disagreements.append(f"{s.key()} -> {t.key()}")
            if here or both_simple:
                rows.append(
                    [
                        s.key(),
                        t.key(),
                        int(here),
                        "" if q is None else " ".join(map(str, q)),
                        int(both_simple),
                        "" if third is None else int(third),
                    ]
                )
            ordered += here
            if here and s != t and reachable(t, s):
                mutual += 1
    tag = run_tag(sameness, bra, bound, rounds)
    _write_csv(
        out / f"reach_{tag}.csv",
        ("from", "to", "reachable", "embedding", "both_assert_nothing_twice", "reachable_under_third_seed"),
        rows,
    )
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(states),
        "ordered_pairs": pairs,
        "rows_written": len(rows),
        "ordered_pairs_reachable": ordered,
        "unordered_pairs_reachable_both_ways": mutual // 2,
        "ordered_pairs_asserting_nothing_twice": simple_pairs,
        "of_which_reachable": simple_reachable,
        "pairs_reachable_with_a_multiplicity_above_one": counted_only,
        "third_derivation_agrees_on_every_pair_asserting_nothing_twice": not third_disagreements,
        "third_derivation_disagreements": third_disagreements,
        "embedding_agrees_with_search": not disagreements,
        "disagreements": disagreements,
    }


def write_counts(out: Path, plan: Plan) -> dict[str, list[int]]:
    """`counts.csv`: results by terms and total multiplicity, by independent count.

    Beside each count, the results asserting nothing twice with that many
    assertions (the third derivation's count, `second.orbits.count_results`).
    """
    rows: list[list[object]] = []
    combos = [(s, b) for s in Sameness for b in (False, True)]
    keys = [f"{s.value}/{alternative(b)}" for s, b in combos]
    totals: dict[str, list[int]] = {key: [] for key in keys}
    for n in range(1, plan.count_upto + 1):
        degree = plan.count_total_upto
        columns = {key: counts_upto(s, b, n, degree) for key, (s, b) in zip(keys, combos)}
        simple = {key: count_simple(s, b, n, degree) for key, (s, b) in zip(keys, combos)}
        for key in keys:
            totals[key].append(sum(columns[key]))
        for t in range(degree + 1):
            rows.append([n, t, *(columns[key][t] for key in keys), *(simple[key][t] for key in keys)])
    _write_csv(
        out / "counts.csv",
        (
            "terms",
            "total_multiplicity",
            *(f"results {key}" for key in keys),
            *(f"asserting nothing twice {key}" for key in keys),
        ),
        rows,
    )
    return totals


def check_free_cost(bound: int, most: int) -> tuple[int, list[str]]:
    """Compare the closed form for FREE cost with the best placement of names.

    Every legal state with at most `bound` terms and no multiplicity above
    `most` is compared, results and non-results alike (both formulas say
    `None` for the latter).
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
