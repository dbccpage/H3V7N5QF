"""Writes `evidence/seventh/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_seventh.py` from the repository root.  No file
holds a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on which changes there are or on what is given.

Cited from the sixth derivation (`sixth.explore`, `sixth.state`,
`sixth.cost`, `sixth.changes`, `sixth.orbits`, `sixth.reach`) and re-checked
by computation
    The sixth derivation's exploration is run beside the seventh's at the
    same bound on terms, from each of its two beginnings and under each of
    its two readings: under any rewriting, the seventh's results with a term
    whose sixth-seed cost is within the sixth's rounds must be exactly the
    sixth's results, each at the round its sixth-seed cost formula gives;
    with the names kept, the sixth's results with the names forgotten must
    be results of the seventh, and every result of the seventh with a term
    and small enough size must be among them (`compare_with_sixth`); the
    sixth's criterion must agree with the seventh's on every pair of results
    with a term (`write_reach`); the sixth's count of changes making some
    `xrx` asserted must equal the seventh's (`write_run`); the sixth's counts
    by destroyed givens must add up to the seventh's counts (`write_counts`).
    This is the computed form of rule 5 for the sixth's computed claims.

Everything about nothing being given — the empty beginning, what a result
adds, the cost as the size, the one irreversible change (leaving the empty
state), the has-a-term criterion, the two-term closed form — is written
afresh.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from sixth.changes import attempt_counts as attempt_counts_sixth
from sixth.explore import explore as explore_sixth
from sixth.orbits import count_free
from sixth.orbits import counts_upto as counts_upto_sixth
from sixth.state import given as given_sixth
from xry.evidence import _write_csv, _write_json, alternative, compare_evidence, write_manifest
from xry.state import Sameness

from seventh.changes import Kind, attempt_counts, first_changes, perform
from seventh.cost import GIVEN_SIZE, cost, cost_sixth, cost_sixth_free, raises_by_one
from seventh.explore import (
    Attempt,
    Exploration,
    count_shortest_sequences,
    cycle,
    explore,
    order,
    performed,
    sequences_exact,
)
from seventh.follows import verdicts
from seventh.invariants import fewest_classes, lowered, size_moves_by_one, term_stays
from seventh.orbits import count_results, counts_within, layer_counts, two_term_count, two_term_round_count
from seventh.reach import reach_graph, reachable, reachable_in_graph, reachable_sixth
from seventh.state import (
    MState,
    added,
    canonical,
    empty,
    forget_canonical_forms,
    forget_names,
    has_term,
    largest_xrx,
    written,
)

__all__ = [
    "ChangeCheck",
    "Plan",
    "added_rows",
    "attempt_record",
    "check_changes",
    "compare_evidence",
    "compare_with_sixth",
    "frontier_rows",
    "one_term_sequences",
    "result_rows",
    "run_tag",
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
    bound on terms are infinite, as under the fourth to sixth seeds).  One
    beginning and one reading, so three explorations in all: the main one
    (`bound` terms, `rounds` rounds), a deeper one with fewer terms
    (`deep_bound`, `deep_rounds`), and one with two terms and
    `two_term_rounds` rounds.  `census_bound`, `census_rounds` give a larger
    run at which only counts are recorded; `census_bound = 0` turns it off.
    Reachability is tested among the results of (`reach_bound`,
    `reach_rounds`) along the changes among the results of (`reach_bound`,
    `reach_rounds + reach_extra`).  The sixth derivation's explorations run
    beside each run with four rounds fewer, so that every sixth result lies
    within the seventh's rounds (its size is at most its sixth-seed cost
    plus four).
    """

    bound: int = 5
    rounds: int = 11
    census_bound: int = 6
    census_rounds: int = 12
    deep_bound: int = 3
    deep_rounds: int = 14
    two_term_rounds: int = 40
    log_bound: int = 2
    log_rounds: int = 4
    reach_bound: int = 3
    reach_rounds: int = 6
    reach_extra: int = 2
    layers_upto: int = 20
    count_upto: int = 6
    count_total_upto: int = 12

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


#: The sixth derivation's explorations run with this many rounds fewer than the seventh's.
SIXTH_ROUNDS_FEWER = 4


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change and its outcome.

    `makes_some_xrx_asserted` says whether the outcome asserts some `xrx`
    while the state asserts none (what the fifth seed would have obstructed;
    a property of the outcome here, as under the sixth).
    """
    return {
        "state": rec.state.key(),
        "written": written(rec.state),
        "round": round_,
        "change": rec.change.written(rec.state),
        "kind": rec.change.kind.value,
        "adds": list(rec.change.additions),
        "changes_a_multiplicity_to": (
            None
            if rec.change.kind not in (Kind.ADD_ASSERTION, Kind.REMOVE)
            else rec.state.mult_of(rec.change.x, rec.change.y) + (1 if rec.change.kind is Kind.ADD_ASSERTION else -1)
        ),
        "makes_some_xrx_asserted": rec.xrx,
        "performed": True,
        "outcome": None if rec.outcome is None else rec.outcome.key(),
        "beyond_bound": rec.beyond,
    }


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the empty beginning, its one change, what it reaches, and the sixth's beginnings seen from here."""
    start = empty()
    first = first_changes()
    expl = explore(start, bound=2, rounds=1, keep_log=True)
    one = MState.of(1, [])
    arb = MState.of(2, [(0, 1)])
    arb_bra = MState.of(2, [(0, 1), (1, 0)])
    loop = MState.of(1, [(0, 0)])
    doc: dict[str, object] = {
        "state": written(start),
        "size": start.size,
        "changes": [c.written(start) for c in first],
        "the_first_change_can_only_add_a_term": [c.kind.value for c in first] == [Kind.ADD_TERM.value],
        "attempts": [attempt_record(rec, 1) for rec in expl.log],
        "results_after_one_change": [written(s) for s, r in sorted(expl.depth.items(), key=lambda kv: order(kv[0])) if r == 1],
        "reaches_the_one_term_state": reachable(start, one),
        "the_one_term_state_reaches_it": reachable(one, start),
        "reaches_itself_in_two_changes": cycle(start) is not None,
        "cost_of_the_one_term_state": cost(one),
        "cost_of_ara_once": cost(loop),
        "the_sixth_seeds_beginnings_seen_from_here": {
            alternative(False): {"state": written(arb), "cost_here": cost(arb), "cost_under_the_sixth_seed": cost_sixth(arb, False)},
            alternative(True): {"state": written(arb_bra), "cost_here": cost(arb_bra), "cost_under_the_sixth_seed": cost_sixth(arb_bra, True)},
        },
        "the_one_term_state_under_the_sixth_seed": {
            alternative(False): cost_sixth(one, False),
            alternative(True): cost_sixth(one, True),
        },
        "the_empty_state_under_the_sixth_seed": cost_sixth_free(start, False),
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "of_which_add_a_term": sum(1 for c in first if c.kind is Kind.ADD_TERM),
        "attempts_not_performed": sum(1 for rec in expl.log if rec.outcome is None and not rec.beyond),
    }


def result_rows(expl: Exploration, sequences: dict[MState, int]) -> list[list[object]]:
    """One row per result."""
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        terms, assertions = added(state)
        attempts, additions = attempt_counts(state)
        rows.append(
            [
                state.key(),
                written(state),
                state.n,
                state.m,
                state.distinct,
                state.most,
                largest_xrx(state),
                terms,
                assertions,
                expl.depth[state],
                cost(state),
                fewest_classes(state) if state.legal else "",
                attempts,
                additions,
                attempt_counts_sixth(state)[1],
                int(expl.depth[state] < expl.rounds),
                sequences[state],
                int(sequences_exact(expl, state)),
                int(has_term(state)),
                int(reachable(state, expl.start)),
                int(reachable(expl.start, state)),
                int(state.simple),
                int(state.legal),
                int(has_term(state)),
                "" if not has_term(state) else cost_sixth(state, False),
                "" if not has_term(state) else cost_sixth(state, True),
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
    "largest_xrx_multiplicity",
    "terms_added_to_given",
    "assertions_added_to_given",
    "round_first_reached",
    "fewest_changes_by_formula",
    "fewest_classes",
    "changes",
    "of_which_additions",
    "changes_making_some_xrx_asserted",
    "changes_attempted",
    "shortest_sequences_of_changes",
    "shortest_sequences_exact_within_bound",
    "has_a_term",
    "reaches_what_is_given",
    "reached_from_what_is_given",
    "asserts_nothing_twice",
    "asserts_no_xrx",
    "is_a_result_of_the_sixth_seed",
    "sixth_seed_cost_without_bra",
    "sixth_seed_cost_with_bra",
)


def added_rows(expl: Exploration) -> list[list[int]]:
    """Results grouped by (terms added, assertions added), fewest additions first."""
    groups: dict[tuple[int, int], list[int]] = {}
    for state, round_ in expl.depth.items():
        groups.setdefault(added(state), []).append(round_)
    ordered = sorted(groups, key=lambda k: (k[0] + k[1], k))
    return [[t, a, len(groups[t, a]), min(groups[t, a]), max(groups[t, a])] for t, a in ordered]


def frontier_rows(expl: Exploration) -> list[list[object]]:
    """One row per frontier state, with how many of its attempts leave the bound on terms."""
    per_state: dict[MState, int] = {}
    for leave in expl.frontier:
        per_state[leave.state] = per_state.get(leave.state, 0) + 1
    return [[state.key(), written(state), expl.depth[state], per_state[state]] for state in sorted(per_state, key=order)]


@dataclass(frozen=True)
class ChangeCheck:
    """What `check_changes` found on every change within the bound."""

    checked: int
    cost_raised_by_more_than_one: tuple[str, ...]
    size_not_moved_by_one: tuple[str, ...]
    cost_rule_disagreements: tuple[str, ...]
    term_lost: tuple[str, ...]
    lowering: dict[str, int]
    round_raised: int
    round_kept: int
    round_lowered: int
    xrx_made: int


def check_changes(expl: Exploration) -> ChangeCheck:
    """On every change within the bound: the cost rises by at most one, and more.

    Checks that the outcome's cost is at most the state's plus one; that the
    size moves by exactly one; that the rule saying which changes raise the
    cost by exactly one (the additions) agrees with the outcome; that a state
    with a term leaves a state with a term; and counts the changes on which
    the earlier derivations' kept counts and properties fall, the changes
    whose outcome is of a lower, the same, or the next round, and the changes
    that make some `xrx` asserted.
    """
    checked = 0
    over: list[str] = []
    stuck: list[str] = []
    wrong: list[str] = []
    lost: list[str] = []
    lowering: dict[str, int] = {}
    raised = kept = fell = made = 0
    for state, change, out in performed(expl):
        checked += 1
        name = f"{state.key()} / {change.written(state)}"
        raw = perform(state, change)
        if cost(raw) > cost(state) + 1:
            over.append(name)
        if not size_moves_by_one(state, raw):
            stuck.append(name)
        if raises_by_one(state, change) != (cost(raw) == cost(state) + 1):
            wrong.append(name)
        if not term_stays(state, raw):
            lost.append(name)
        for what in lowered(state, raw):
            lowering[what] = lowering.get(what, 0) + 1
        made += state.legal and not raw.legal
        step = expl.depth[out] - expl.depth[state]
        if step > 0:
            raised += 1
        elif step == 0:
            kept += 1
        else:
            fell += 1
    return ChangeCheck(
        checked, tuple(over), tuple(stuck), tuple(wrong), tuple(lost), dict(sorted(lowering.items())), raised, kept, fell, made
    )


def one_term_sequences(expl: Exploration, sequences: dict[MState, int]) -> bool:
    """Every result with one term is reached by exactly one shortest sequence (add a term, then `ara`)."""
    return all(sequences[s] == 1 for s in expl.depth if s.n == 1)


def compare_with_sixth(expl: Exploration, bra: bool) -> dict[str, object]:
    """The seventh's results with a term against the sixth derivation's exploration.

    The sixth's explorations (from `arb` alone or with `bra`, under any
    rewriting and with the names kept) are run at the seventh's bound on
    terms with `SIXTH_ROUNDS_FEWER` rounds fewer, so every sixth result lies
    within the seventh's rounds.  Under any rewriting: the seventh's results
    with a term whose sixth-seed cost is within the sixth's rounds must be
    exactly the sixth's results, each at the round its sixth-seed cost gives.
    With the names kept: the sixth's results with their names forgotten must
    all be results of the seventh, and every result of the seventh with a
    term and size at most the sixth's rounds minus the largest destroyed
    givens (one without `bra`, two with) must be among them.
    """
    if expl.bound < 2:
        raise ValueError("the sixth seed's beginnings have two terms")
    sixth_rounds = max(expl.rounds - SIXTH_ROUNDS_FEWER, 0)
    free = explore_sixth(given_sixth(bra, Sameness.FREE), expl.bound, sixth_rounds)
    ours = {s for s in expl.depth if has_term(s) and cost_sixth(s, bra) <= sixth_rounds}
    same_results = ours == set(free.depth)
    rounds_agree = all(free.depth[s] == cost_sixth(s, bra) for s in ours if s in free.depth)
    anchored = explore_sixth(given_sixth(bra, Sameness.ANCHORED), expl.bound, sixth_rounds)
    forgotten = {canonical(forget_names(s)) for s in anchored.depth}
    small = {s for s in expl.depth if has_term(s) and s.size + (2 if bra else 1) <= sixth_rounds}
    return {
        "sixth_rounds": sixth_rounds,
        "sixth_results_any_rewriting": len(free.depth),
        "results_with_a_term_within_the_sixth_rounds": len(ours),
        "same_results_as_sixth_derivation_any_rewriting": same_results,
        "sixth_round_is_its_cost_formula_on_every_shared_result": rounds_agree,
        "sixth_results_names_kept": len(anchored.depth),
        "sixth_results_names_forgotten": len(forgotten),
        "sixth_results_names_forgotten_are_results": forgotten <= set(expl.depth),
        "results_with_a_term_of_small_size": len(small),
        "results_with_a_term_of_small_size_are_sixth_results_names_forgotten": small <= forgotten,
        "results_where_the_sixth_cost_equals_the_cost": sum(1 for s in expl.depth if has_term(s) and cost_sixth(s, bra) == cost(s)),
    }


def sixth_ok(block: dict[str, object]) -> bool:
    """Every comparison with the sixth derivation passes."""
    return bool(
        block["same_results_as_sixth_derivation_any_rewriting"]
        and block["sixth_round_is_its_cost_formula_on_every_shared_result"]
        and block["sixth_results_names_forgotten_are_results"]
        and block["results_with_a_term_of_small_size_are_sixth_results_names_forgotten"]
    )


def _by_terms_total(expl: Exploration) -> dict[str, int]:
    """Explored results by (terms, total multiplicity), as text keys."""
    out: dict[str, int] = {}
    for state in expl.depth:
        key = f"{state.n}/{state.m}"
        out[key] = out.get(key, 0) + 1
    return out


def write_run(out: Path, bound: int, rounds: int, plan: Plan) -> dict[str, object]:
    """All files of one exploration (`bound` terms, `rounds` rounds); returns its summary."""
    tag = run_tag(bound, rounds)
    expl = explore(empty(), bound, rounds)
    sequences = count_shortest_sequences(expl)

    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, sequences))
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

    exact = layer_counts(min(plan.layers_upto, rounds))
    legal_per_round = [0] * (rounds + 1)
    for state, r in expl.depth.items():
        legal_per_round[r] += state.legal
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
                legal_per_round[r],
                exact[r] if r < len(exact) else "",
                two_term_round_count(r) if bound == 2 else "",
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
            "new_results_asserting_no_xrx",
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
                "" if v.holds_at is None else written(v.holds_at),
                "" if v.holds_round is None else v.holds_round,
                "" if v.fails_at is None else written(v.fails_at),
                "" if v.fails_round is None else v.fails_round,
            ]
            for v in found
        ],
    )

    by_terms: dict[int, int] = {}
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s) != r]
    # A result of round r has at most r terms, so rounds 0 .. N are complete within N terms.
    within_bound_layers = min(len(exact) - 1, bound, rounds)
    entries: dict[MState, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s, r in expl.depth.items() if s.n == bound and r < rounds}
    one_each = set(entries) == full and all(c == 1 for c in entries.values())
    edges = check_changes(expl)
    tried = [s for s, r in expl.depth.items() if r < rounds]
    awaiting = expl.awaiting
    two_term_closed = expl.new_per_round == [two_term_round_count(r) for r in range(rounds + 1)] if bound == 2 else None
    round_one = [s for s, r in expl.depth.items() if r == 1]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_asserting_some_xrx": sum(1 for s in expl.depth if not s.legal),
        "results_with_a_term": sum(1 for s in expl.depth if has_term(s)),
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": _by_terms_total(expl) == counts_within(bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "rounds_agreeing_with_unbounded_formula": [expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)],
        "two_term_rounds_equal_closed_form": two_term_closed,
        "the_first_round_is_the_one_term_state_alone": round_one == [MState.of(1, [])] if rounds >= 1 else None,
        "attempts_equal_formula": expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried),
        "additions_attempted": sum(attempt_counts(s)[1] for s in tried),
        "xrx_making_equal_sixth_formula": expl.xrx_per_round[-1] == sum(attempt_counts_sixth(s)[1] for s in tried),
        "attempts_obstructed": 0,
        "frontier_states": len(entries),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_per_state_with_N_terms": one_each,
        "results_of_the_last_round_whose_changes_await": len(awaiting),
        "changes_awaiting": sum(attempt_counts(s)[0] for s in awaiting),
        "changes_checked": edges.checked,
        "changes_making_some_xrx_asserted": edges.xrx_made,
        "cost_raised_by_more_than_one": list(edges.cost_raised_by_more_than_one),
        "size_not_moved_by_one": list(edges.size_not_moved_by_one),
        "cost_rule_disagreements": list(edges.cost_rule_disagreements),
        "term_lost": list(edges.term_lost),
        "changes_lowering": edges.lowering,
        "changes_raising_the_round": edges.round_raised,
        "changes_keeping_the_round": edges.round_kept,
        "changes_lowering_the_round": edges.round_lowered,
        "results_with_a_two_change_cycle": sum(1 for s in expl.depth if cycle(s) is not None),
        "shortest_sequences_total": sum(sequences.values()),
        "results_reached_by_one_shortest_sequence": sum(1 for c in sequences.values() if c == 1),
        "results_with_exact_sequence_count": sum(1 for s in expl.depth if sequences_exact(expl, s)),
        "one_term_results_have_one_shortest_sequence": one_term_sequences(expl, sequences),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "results_reached_from_what_is_given": sum(1 for s in expl.depth if reachable(expl.start, s)),
        "sixth_derivation": {alternative(bra): compare_with_sixth(expl, bra) for bra in (False, True)},
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results, completeness, cost formula, the sixth's.

    No per-result file is written; the frontier is counted, not exported.
    """
    expl = explore(empty(), bound, rounds)
    by_terms: dict[int, int] = {}
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s) != r]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_asserting_some_xrx": sum(1 for s in expl.depth if not s.legal),
        "last_round_with_a_new_result": expl.last_new_round,
        "changes_attempted": expl.attempts_per_round[-1],
        "of_which_making_some_xrx_asserted": expl.xrx_per_round[-1],
        "explored_equals_independent_count": _by_terms_total(expl) == counts_within(bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "frontier_states": len({leave.state for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
        "results_of_the_last_round_whose_changes_await": len(expl.awaiting),
        "sixth_derivation": {alternative(bra): compare_with_sixth(expl, bra) for bra in (False, True)},
    }


def write_log(out: Path, plan: Plan) -> int:
    """The full attempt log of a small exploration (`plan.log_bound` terms, `plan.log_rounds` rounds)."""
    expl = explore(empty(), plan.log_bound, plan.log_rounds, keep_log=True)
    tag = run_tag(plan.log_bound, plan.log_rounds)
    path = out / f"attempts_{tag}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in expl.log:
            line = attempt_record(rec, expl.depth[rec.state] + 1)
            handle.write(json.dumps(line, sort_keys=True, ensure_ascii=True) + "\n")
    return len(expl.log)


def write_reach(out: Path, plan: Plan) -> dict[str, object]:
    """`reach_{tag}.csv`: what each result reaches, by the has-a-term criterion and by search.

    The results are those of (`reach_bound`, `reach_rounds`); the search
    follows the changes among the results of (`reach_bound`, `reach_rounds +
    reach_extra`), enough for every sequence the paper's proof of the
    criterion uses.  Every ordered pair is tested both ways; the file has one
    row per result with the counts, and the totals are in the summary, with
    the comparison with the sixth derivation's criterion on the pairs of
    results with a term.
    """
    bound, rounds = plan.reach_bound, plan.reach_rounds
    start = empty()
    expl = explore(start, bound, rounds)
    wide = explore(start, bound, rounds + plan.reach_extra)
    graph = reach_graph(wide)
    states = sorted(expl.depth, key=lambda s: (expl.depth[s], order(s)))
    inside = set(states)
    disagreements: list[str] = []
    sixth_disagreements: list[str] = []
    reached_by: dict[MState, int] = {s: 0 for s in states}
    reaches: dict[MState, int] = {}
    found_counts: dict[MState, int] = {}
    ordered = mutual = 0
    sixth_pairs = sixth_reachable = 0
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
            if has_term(s) and has_term(t):
                sixth_pairs += 1
                before = reachable_sixth(s, t)
                sixth_reachable += before
                if before != here:
                    sixth_disagreements.append(f"{s.key()} -> {t.key()}")
        reaches[s] = here_count
        ordered += here_count
    rows: list[list[object]] = [
        [
            s.key(),
            written(s),
            expl.depth[s],
            int(has_term(s)),
            int(s.legal),
            reaches[s],
            reached_by[s],
            found_counts[s],
            int(reaches[s] == found_counts[s]),
            int(reachable(s, expl.start)),
            int(has_term(s)),
        ]
        for s in states
    ]
    tag = run_tag(bound, rounds)
    _write_csv(
        out / f"reach_{tag}.csv",
        (
            "state",
            "written",
            "round",
            "has_a_term",
            "asserts_no_xrx",
            "results_it_reaches",
            "results_reaching_it",
            "results_it_reaches_by_search",
            "criterion_agrees_with_search",
            "reaches_what_is_given",
            "is_a_result_of_the_sixth_seed",
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
        "results_with_a_term": sum(1 for s in states if has_term(s)),
        "results_asserting_some_xrx": sum(1 for s in states if not s.legal),
        "criterion_agrees_with_search": not disagreements,
        "disagreements": disagreements,
        "ordered_pairs_of_results_with_a_term": sixth_pairs,
        "of_which_reachable_under_the_sixth_seed": sixth_reachable,
        "sixth_criterion_agrees_on_results_with_a_term": not sixth_disagreements,
        "sixth_criterion_disagreements": sixth_disagreements,
        "results_that_reach_what_is_given": sum(1 for s in states if reachable(s, expl.start)),
    }


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and total multiplicity, by independent count.

    All results (every well-formed state, the empty one included) up to
    rewriting, beside the number of them asserting no `xrx` (the fifth and
    sixth derivations' count) and, with two terms, the closed form.  The
    sixth derivation's counts by destroyed givens (either beginning, either
    reading) must add up to these counts for every `n ≥ 1`.
    """
    rows: list[list[object]] = []
    totals: list[int] = []
    degree = plan.count_total_upto
    closed_form_mismatches: list[str] = []
    sixth_add_up = True
    for n in range(plan.count_upto + 1):
        every = count_results(n, degree)
        legal = count_results_no_xrx(n, degree)
        totals.append(sum(every))
        if n >= 1:
            for bra in (False, True):
                sixth_add_up = sixth_add_up and counts_upto_sixth(Sameness.FREE, bra, n, degree) == every
        for t in range(degree + 1):
            closed = two_term_count(t) if n == 2 else ""
            if n == 2 and closed != every[t]:
                closed_form_mismatches.append(f"2/{t}")
            rows.append([n, t, every[t], legal[t], closed])
    _write_csv(
        out / "counts.csv",
        ("terms", "total_multiplicity", "results", "results asserting no xrx", "results by the two-term closed form"),
        rows,
    )
    return {
        "totals_by_terms": totals,
        "two_term_closed_form_mismatches": closed_form_mismatches,
        "sixth_counts_by_destroyed_givens_add_up_to_these": sixth_add_up,
    }


def count_results_no_xrx(n: int, degree: int) -> list[int]:
    """Results with `n` terms asserting no `xrx`, by total multiplicity (the sixth's capped count)."""
    return count_free(n, degree, cap=0)


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    summary: dict[str, object] = {
        "plan": {
            "bound_on_terms": plan.bound,
            "rounds": plan.rounds,
            "census_bound_on_terms": plan.census_bound,
            "census_rounds": plan.census_rounds,
            "deep_run_bound_on_terms": plan.deep_bound,
            "deep_run_rounds": plan.deep_rounds,
            "two_term_run_rounds": plan.two_term_rounds,
            "full_log_bound_on_terms": plan.log_bound,
            "full_log_rounds": plan.log_rounds,
            "reachability_bound_on_terms": plan.reach_bound,
            "reachability_rounds": plan.reach_rounds,
            "reachability_search_rounds": plan.reach_rounds + plan.reach_extra,
            "unbounded_round_counts_upto": plan.layers_upto,
            "sixth_derivation_rounds_fewer": SIXTH_ROUNDS_FEWER,
            "size_of_what_is_given": GIVEN_SIZE,
        },
        "given": write_given(out),
        "independent_counts": write_counts(out, plan),
    }
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan)
        forget_canonical_forms()
    summary["runs"] = runs
    summary["reachability"] = write_reach(out, plan)
    summary["attempts_in_full_log"] = write_log(out, plan)
    census: dict[str, object] = {}
    if plan.census_bound > plan.bound:
        census[run_tag(plan.census_bound, plan.census_rounds)] = write_census(plan.census_bound, plan.census_rounds)
        forget_canonical_forms()
    summary["census"] = census
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
