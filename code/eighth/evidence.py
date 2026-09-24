"""Writes `evidence/eighth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_eighth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest, `compare_evidence` and
    `alternative` do not depend on which changes there are.

Cited from the sixth derivation (`sixth.explore`, `sixth.cost`,
`sixth.orbits`, `sixth.reach`) and re-checked by computation
    The sixth derivation's exploration is run beside the eighth's at the same
    bound and rounds; the eighth's results asserting nothing with `s` must be
    the sixth's results, at the same rounds, with the same numbers of
    shortest sequences (`compare_with_sixth`); the sixth's cost of the `r`
    part plus the `s` total must be the round of every result (`write_run`);
    the sixth's count of changes making some `xrx` asserted must equal the
    eighth's per relation (`write_run`); the sixth's counts must be the
    eighth's with the `s` factor removed, and must differ from the eighth's
    counts by more than a product for two or more terms (`write_counts`).
    This is the computed form of rule 5 for the sixth's computed claims.

Everything about the second relation — the attempt records (whether the
outcome asserts some `xrx`, some `xsx`), the result rows with both totals,
the joint statements, the two-term closed forms with the `s` items, the
product count — is written afresh.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from itertools import product
from math import factorial
from pathlib import Path

from sixth.explore import Exploration as ExplorationSixth
from sixth.explore import count_shortest_sequences as count_shortest_sequences_sixth
from sixth.explore import explore as explore_sixth
from sixth.orbits import count_free as count_free_part
from sixth.state import given as given_sixth
from xry.evidence import _write_csv, _write_json, alternative, compare_evidence, write_manifest
from xry.state import Sameness

from eighth.changes import Change, Kind, attempt_counts, changes, perform
from eighth.cost import cost, cost_free_by_placement, destroyed, raises_by_one
from eighth.explore import Attempt, Exploration, count_shortest_sequences, cycle, explore, order, performed, sequences_exact
from eighth.follows import verdicts
from eighth.invariants import cost_rises_by_at_most_one, fewest_classes, lowered, names_stay_merged
from eighth.orbits import APART_KINDS, NAMED_KINDS, count_free, count_named, counts_within, layer_counts, product_count, two_term_round_count
from eighth.reach import reach_graph, reachable, reachable_in_graph
from eighth.state import DState, MState, added, canonical, forget_canonical_forms, given, names_one_term, of_r

__all__ = [
    "ChangeCheck",
    "Plan",
    "added_rows",
    "attempt_record",
    "check_changes",
    "check_free_cost",
    "compare_evidence",
    "compare_with_sixth",
    "frontier_rows",
    "result_rows",
    "run_tag",
    "two_term_multinomial",
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

    Every exploration is bounded in terms and in rounds.  Three explorations
    per beginning and reading: the main one (`free_bound` / `anchored_bound`
    terms, `rounds` rounds), a deeper one with fewer terms (`deep_bound`,
    `deep_rounds`), and one with the given terms only and `two_term_rounds`
    rounds.  `census_bound` is a larger bound for the ANCHORED runs at which
    only counts are recorded; `0` turns the census off.  Reachability is
    tested among the results of (`reach_bound`, `reach_rounds`) along the
    changes among the results of (`reach_bound`, `reach_rounds + reach_extra`).
    """

    free_bound: int = 4
    anchored_bound: int = 3
    rounds: int = 5
    census_bound: int = 4
    deep_bound: int = 3
    deep_rounds: int = 6
    two_term_rounds: int = 8
    log_bound: int = 2
    log_rounds: int = 3
    reach_bound: int = 2
    reach_rounds: int = 4
    reach_extra: int = 3
    layers_upto: int = 12
    count_upto: int = 4
    count_total_upto: int = 8

    def bound(self, sameness: Sameness) -> int:
        """The declared bound on the number of terms under `sameness`."""
        return self.free_bound if sameness is Sameness.FREE else self.anchored_bound

    def runs(self, sameness: Sameness) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the explorations written for `sameness`."""
        return ((self.bound(sameness), self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(sameness: Sameness, bra: bool, bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}_{sameness.value}_{alternative(bra)}"


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change and its outcome, with the relation of an assertion."""
    return {
        "state": rec.state.key(),
        "written": rec.state.written(),
        "round": round_,
        "change": rec.change.written(rec.state),
        "kind": rec.change.kind.value,
        "relation": rec.change.rel or None,
        "adds": list(rec.change.additions),
        "changes_a_multiplicity_to": (
            None
            if rec.change.kind not in (Kind.ADD_ASSERTION, Kind.REMOVE)
            else rec.state.mult_of(rec.change.rel, rec.change.x, rec.change.y)
            + (1 if rec.change.kind is Kind.ADD_ASSERTION else -1)
        ),
        "makes_some_xrx_asserted": rec.xrx,
        "makes_some_xsx_asserted": rec.xsx,
        "performed": True,
        "outcome": None if rec.outcome is None else rec.outcome.key(),
        "beyond_bound": rec.beyond,
    }


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the alternatives for what is given, every attempt on them, what they reach."""
    doc: dict[str, object] = {
        "states_on_the_given_terms": "infinite: any multiplicities of the four r pairs and the four s pairs; the names one term with ara, asa any number of times",
        "results_among_them": "all of them (every well-formed two-relation state with at least one term is a result)",
    }
    not_performed = 0
    off_formula = 0
    for sameness in Sameness:
        for bra in (False, True):
            start = given(bra, sameness)
            expl = explore(start, bound=3, rounds=1, keep_log=True)
            listed = changes(start)
            attempts, xrx, xsx = attempt_counts(start)
            not_performed += sum(1 for rec in expl.log if rec.outcome is None and not rec.beyond)
            off_formula += int((sum(1 for rec in expl.log if rec.xrx), sum(1 for rec in expl.log if rec.xsx)) != (xrx, xsx))
            merged = perform(start, Change(Kind.IDENTIFY, "", 0, 1))
            with_asb = perform(start, Change(Kind.ADD_ASSERTION, "s", 0, 1))
            with_asa = perform(start, Change(Kind.ADD_ASSERTION, "s", 0, 0))
            one = DState.of(1, [], [], None if start.names is None else (0, 0))
            doc[f"{sameness.value}/{alternative(bra)}"] = {
                "state": start.written(),
                "changes": attempts,
                "of_which_in_r": sum(c.rel == "r" for c in listed),
                "of_which_in_s": sum(c.rel == "s" for c in listed),
                "of_which_make_some_xrx_asserted": xrx,
                "of_which_make_some_xsx_asserted": xsx,
                "of_which_obstructed": 0,
                "attempts": [attempt_record(rec, 1) for rec in expl.log],
                "identifying_a_and_b_gives": merged.written(),
                "cost_of_identifying_a_and_b": cost(merged, bra),
                "adding_asb_gives": with_asb.written(),
                "cost_of_adding_asb": cost(with_asb, bra),
                "adding_asa_gives": with_asa.written(),
                "cost_of_adding_asa": cost(with_asa, bra),
                "reaches_the_other_beginning": reachable(start, given(not bra, sameness)),
                "reaches_the_one_term_state": reachable(start, one),
                "the_one_term_state_reaches_it": reachable(one, start),
                "asb_given_instead_reaches_it": reachable(with_asb, start),
                "it_reaches_asb_given_instead": reachable(start, with_asb),
            }
    _write_json(out / "given.json", doc)
    return {"attempts_not_performed": not_performed, "beginnings_whose_loop_counts_differ_from_formula": off_formula}


def result_rows(expl: Exploration, bra: bool, sequences: dict[DState, int], sixth: dict[MState, int]) -> list[list[object]]:
    """One row per result."""
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        terms, assertions = added(state)
        attempts, xrx, xsx = attempt_counts(state)
        c = cost(state, bra)
        rows.append(
            [
                state.key(),
                state.written(),
                state.n,
                state.m,
                state.total_r,
                state.total_s,
                state.distinct,
                state.most,
                terms,
                assertions,
                expl.depth[state],
                "" if c is None else c,
                "" if c is None else c - state.total_s,
                destroyed(state, bra),
                fewest_classes(state.r_part()) if state.legal_r else "",
                fewest_classes(state.s_part()) if state.legal_s else "",
                attempts,
                xrx,
                xsx,
                int(expl.depth[state] < expl.rounds),
                sequences[state],
                int(sequences_exact(expl, state, bra)),
                int(reachable(state, expl.start)),
                int(names_one_term(state)),
                int(state.nothing_in_s),
                int(state.simple),
                int(state.legal_r),
                int(state.legal_s),
                sixth.get(state.r_part(), "") if state.nothing_in_s else "",
            ]
        )
    return rows


RESULT_HEADER = (
    "state",
    "written",
    "terms",
    "assertions_counted",
    "assertions_in_r",
    "assertions_in_s",
    "assertions_asserted",
    "largest_multiplicity",
    "terms_added_to_given",
    "assertions_added_to_given",
    "round_first_reached",
    "fewest_changes_by_formula",
    "fewest_changes_of_the_r_part_sixth_seed",
    "destroyed_givens",
    "fewest_classes_r",
    "fewest_classes_s",
    "changes",
    "changes_making_some_xrx_asserted",
    "changes_making_some_xsx_asserted",
    "changes_attempted",
    "shortest_sequences_of_changes",
    "shortest_sequences_exact_within_bound",
    "reaches_what_is_given",
    "names_one_term",
    "nothing_in_s",
    "asserts_nothing_twice",
    "asserts_no_xrx",
    "asserts_no_xsx",
    "shortest_sequences_sixth_seed",
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
    per_state: dict[DState, int] = {}
    for leave in expl.frontier:
        per_state[leave.state] = per_state.get(leave.state, 0) + 1
    return [[state.key(), state.written(), expl.depth[state], per_state[state]] for state in sorted(per_state, key=order)]


@dataclass(frozen=True)
class ChangeCheck:
    """What `check_changes` found on every change within the bound."""

    checked: int
    cost_raised_by_more_than_one: tuple[str, ...]
    cost_rule_disagreements: tuple[str, ...]
    names_told_apart_again: tuple[str, ...]
    lowering: dict[str, int]
    round_raised: int
    round_kept: int
    round_lowered: int
    xrx_made: int
    xsx_made: int


def check_changes(expl: Exploration, bra: bool) -> ChangeCheck:
    """On every change within the bound: the cost rises by at most one, and more."""
    checked = 0
    over: list[str] = []
    wrong: list[str] = []
    apart: list[str] = []
    lowering: dict[str, int] = {}
    raised = kept = fell = made_r = made_s = 0
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
        made_r += state.legal_r and not raw.legal_r
        made_s += state.legal_s and not raw.legal_s
        step = expl.depth[out] - expl.depth[state]
        if step > 0:
            raised += 1
        elif step == 0:
            kept += 1
        else:
            fell += 1
    return ChangeCheck(checked, tuple(over), tuple(wrong), tuple(apart), dict(sorted(lowering.items())), raised, kept, fell, made_r, made_s)


def compare_with_sixth(
    expl: Exploration, sixth: ExplorationSixth, sequences: dict[DState, int], sixth_sequences: dict[MState, int]
) -> dict[str, object]:
    """The results asserting nothing with `s` against the sixth derivation's exploration.

    Both explorations must have the same bound on terms and the same rounds.
    The results asserting nothing with `s`, read as their `r` parts, with
    their rounds, must be exactly the sixth's results with their rounds; the
    number of shortest sequences reaching each must be the sixth's (a shortest
    sequence to such a result never touches `s`).
    """
    ours = {s.r_part(): r for s, r in expl.depth.items() if s.nothing_in_s}
    rounds_agree = ours == sixth.depth
    counts = {s.r_part(): sequences[s] for s in expl.depth if s.nothing_in_s}
    sequences_agree = rounds_agree and all(counts[p] == sixth_sequences[p] for p in ours)
    return {
        "results_asserting_nothing_with_s": len(ours),
        "sixth_derivation_results": len(sixth.depth),
        "same_results_and_rounds_as_sixth_derivation": rounds_agree,
        "same_shortest_sequence_counts_as_sixth_derivation": sequences_agree,
        "results_whose_r_part_is_what_is_given": sum(1 for s in expl.depth if s.r_part() == expl.start.r_part()),
    }


def _by_lost(expl: Exploration, bra: bool) -> dict[str, int]:
    """Explored results by (terms, total multiplicity, destroyed givens), as text keys."""
    out: dict[str, int] = {}
    for state in expl.depth:
        key = f"{state.n}/{state.m}/{destroyed(state, bra)}"
        out[key] = out.get(key, 0) + 1
    return out


def two_term_multinomial(expl: Exploration, sequences: dict[DState, int], bra: bool) -> bool | None:
    """On two-term results with names apart: the shortest sequences are the arrangements of the cost-raising changes.

    The sixth's four `r` items (each given: `M − 1` additions if asserted, one
    removal if not; `bra` when not given, `ara`, `brb`: their multiplicities)
    and the four `s` items (`asa`, `asb`, `bsa`, `bsb`: their multiplicities);
    the count is the multinomial coefficient.
    """
    if expl.start.names is None:
        return None
    for state in expl.depth:
        if state.n != 2 or state.names is None or names_one_term(state):
            continue
        a, b = state.names
        items: list[int] = []
        for x, y, is_given in ((a, b, True), (b, a, bra)):
            k = state.mult_of("r", x, y)
            items.append(k - 1 if is_given and k >= 1 else (1 if is_given else k))
        items += [state.mult_of("r", a, a), state.mult_of("r", b, b)]
        items += [state.mult_of("s", x, y) for x in (a, b) for y in (a, b)]
        expected = factorial(sum(items))
        for k in items:
            expected //= factorial(k)
        if sequences[state] != expected:
            return False
    return True


def write_run(out: Path, sameness: Sameness, bra: bool, bound: int, rounds: int, plan: Plan) -> dict[str, object]:
    """All files of one exploration (`bound` terms, `rounds` rounds); returns its summary."""
    tag = run_tag(sameness, bra, bound, rounds)
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    sixth = explore_sixth(given_sixth(bra, sameness), bound, rounds)
    sequences = count_shortest_sequences(expl)
    sixth_sequences = count_shortest_sequences_sixth(sixth)

    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, bra, sequences, sixth_sequences))
    _write_csv(
        out / f"added_{tag}.csv",
        ("terms_added_to_given", "assertions_added_to_given", "results", "first_round", "last_round"),
        added_rows(expl),
    )
    _write_csv(
        out / f"frontier_{tag}.csv",
        ("state", "written", "round_first_reached", "leaves_by_the_change"),
        frontier_rows(expl),
    )

    exact = layer_counts(sameness, bra, min(plan.layers_upto, rounds))
    only_r_per_round = [0] * (rounds + 1)
    merged_per_round = [0] * (rounds + 1)
    for state, r in expl.depth.items():
        only_r_per_round[r] += state.nothing_in_s
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
                expl.xrx_per_round[r],
                expl.xsx_per_round[r],
                only_r_per_round[r],
                sixth.new_per_round[r],
                merged_per_round[r],
                exact[r] if r < len(exact) else "",
                two_term_round_count(bra, r) if bound == 2 and sameness is Sameness.ANCHORED else "",
            ]
        )
    _write_csv(
        out / f"rounds_{tag}.csv",
        (
            "round",
            "new_results_within_bound",
            "results_so_far_within_bound",
            "changes_attempted_so_far",
            "of_which_making_some_xrx_asserted",
            "of_which_making_some_xsx_asserted",
            "new_results_asserting_nothing_with_s",
            "new_results_sixth_derivation",
            "new_results_with_the_names_one_term",
            "new_results_without_bound_by_formula",
            "new_results_with_two_terms_by_closed_form",
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
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    within_bound_layers = min(len(exact) - 1, bound - 2, rounds)
    entries: dict[DState, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s, r in expl.depth.items() if s.n == bound and r < rounds}
    one_each = set(entries) == full and all(c == 1 for c in entries.values())
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
        "results_asserting_some_xrx": sum(1 for s in expl.depth if not s.legal_r),
        "results_asserting_some_xsx": sum(1 for s in expl.depth if not s.legal_s),
        "results_asserting_nothing_with_s": sum(only_r_per_round),
        "results_asserting_nothing_with_r": sum(1 for s in expl.depth if s.total_r == 0),
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": _by_lost(expl, bra) == counts_within(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "rounds_agreeing_with_unbounded_formula": [expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)],
        "two_term_rounds_equal_closed_form": two_term_closed,
        **compare_with_sixth(expl, sixth, sequences, sixth_sequences),
        "results_with_the_names_one_term": sum(merged_per_round),
        "attempts_equal_formula": expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried),
        "xrx_making_equal_sixth_formula": expl.xrx_per_round[-1] == sum(attempt_counts(s)[1] for s in tried),
        "xsx_making_equal_sixth_formula": expl.xsx_per_round[-1] == sum(attempt_counts(s)[2] for s in tried),
        "attempts_obstructed": 0,
        "frontier_states": len(entries),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_per_state_with_N_terms": one_each,
        "results_of_the_last_round_whose_changes_await": len(awaiting),
        "changes_awaiting": sum(attempt_counts(s)[0] for s in awaiting),
        "changes_checked": edges.checked,
        "changes_making_some_xrx_asserted": edges.xrx_made,
        "changes_making_some_xsx_asserted": edges.xsx_made,
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
        "results_with_exact_sequence_count": sum(1 for s in expl.depth if sequences_exact(expl, s, bra)),
        "two_term_sequences_equal_multinomial": two_term_multinomial(expl, sequences, bra),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results, completeness, cost formula, the sixth's."""
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    sixth = explore_sixth(given_sixth(bra, sameness), bound, rounds)
    sequences = count_shortest_sequences(expl)
    sixth_sequences = count_shortest_sequences_sixth(sixth)
    by_terms: dict[int, int] = {}
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_asserting_nothing_with_s": sum(1 for s in expl.depth if s.nothing_in_s),
        "last_round_with_a_new_result": expl.last_new_round,
        "changes_attempted": expl.attempts_per_round[-1],
        "explored_equals_independent_count": _by_lost(expl, bra) == counts_within(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        **compare_with_sixth(expl, sixth, sequences, sixth_sequences),
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
    """`reach_{tag}.csv`: what each result reaches, by the names criterion on the `r` part and by search.

    Every ordered pair of results of (`reach_bound`, `reach_rounds`) is
    tested both ways along the changes among the results of (`reach_bound`,
    `reach_rounds + reach_extra`); the pairs whose `r` parts are the same are
    counted apart (they must all reach each other: the `s` part imposes
    nothing).
    """
    bound, rounds = plan.reach_bound, plan.reach_rounds
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    wide = explore(start, bound, rounds + plan.reach_extra)
    graph = reach_graph(wide)
    states = sorted(expl.depth, key=lambda s: (expl.depth[s], order(s)))
    inside = set(states)
    disagreements: list[str] = []
    reached_by: dict[DState, int] = {s: 0 for s in states}
    reaches: dict[DState, int] = {}
    found_counts: dict[DState, int] = {}
    ordered = mutual = 0
    same_r_pairs = same_r_mutual = 0
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
            both = here and reachable(t, s)
            mutual += both
            if s.r_part() == t.r_part() and s != t:
                same_r_pairs += 1
                same_r_mutual += both
        reaches[s] = here_count
        ordered += here_count
    rows: list[list[object]] = [
        [
            s.key(),
            s.written(),
            expl.depth[s],
            int(names_one_term(s)),
            int(s.nothing_in_s),
            reaches[s],
            reached_by[s],
            found_counts[s],
            int(reaches[s] == found_counts[s]),
            int(reachable(s, expl.start)),
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
            "nothing_in_s",
            "results_it_reaches",
            "results_reaching_it",
            "results_it_reaches_by_search",
            "criterion_agrees_with_search",
            "reaches_what_is_given",
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
        "ordered_pairs_with_the_same_r_part": same_r_pairs,
        "of_which_reachable_both_ways": same_r_mutual,
        "results_that_reach_what_is_given": sum(1 for s in states if reachable(s, expl.start)),
    }


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and total multiplicity, by independent count.

    All results under each reading, split by how the named terms stand,
    beside the sixth derivation's single-relation counts and their product
    (which the two-relation count exceeds for two or more terms: the
    rewriting acts on both relations at once).
    """
    rows: list[list[object]] = []
    totals: dict[str, list[int]] = {"free": [], "anchored": [], "product": []}
    product_equals_for_one_term = True
    product_differs_beyond_one_term = True
    degree = plan.count_total_upto
    for n in range(1, plan.count_upto + 1):
        free_all = count_free(n, degree)
        named = count_named(n, degree)
        single = count_free_part(n, degree)
        prod = product_count(n, degree)
        totals["free"].append(sum(free_all))
        totals["anchored"].append(sum(sum(v) for v in named.values()))
        totals["product"].append(sum(prod))
        if n == 1:
            product_equals_for_one_term = product_equals_for_one_term and free_all == prod
        else:
            product_differs_beyond_one_term = product_differs_beyond_one_term and any(f > p for f, p in zip(free_all, prod)) and all(f >= p for f, p in zip(free_all, prod))
        for t in range(degree + 1):
            rows.append([n, t, free_all[t], *(named[kind][t] for kind in NAMED_KINDS), single[t], prod[t]])
    _write_csv(
        out / "counts.csv",
        (
            "terms",
            "total_multiplicity",
            "results free",
            *(f"results anchored: {k}" for k in NAMED_KINDS),
            "sixth seed results free (one relation)",
            "product of the single-relation counts",
        ),
        rows,
    )
    return {
        "totals": totals,
        "product_equals_count_for_one_term": product_equals_for_one_term,
        "count_exceeds_product_for_two_or_more_terms": product_differs_beyond_one_term,
        "apart_kinds": list(APART_KINDS),
    }


def check_free_cost(bound: int, most: int) -> tuple[int, list[str]]:
    """Compare the closed form for FREE cost with the best placement of names, both relations filled."""
    checked = 0
    mismatches = []
    for bra in (False, True):
        for n in range(1, bound + 1):
            seen: set[DState] = set()
            for r in product(range(most + 1), repeat=n * n):
                for s in product(range(most + 1), repeat=n * n):
                    state = canonical(DState(n, r, s))
                    if state in seen:
                        continue
                    seen.add(state)
                    if cost(state, bra) != cost_free_by_placement(state, bra):
                        mismatches.append(f"{alternative(bra)}/{state.key()}")
                    checked += 1
    return checked, mismatches


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    checked, cost_mismatches = check_free_cost(2, 2)
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
