"""Writes `evidence/ninth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_ninth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on which changes there are, on what is given, or on how many
    relations there are.

Cited from the seventh derivation (`seventh.explore`, `seventh.state`,
`seventh.orbits`, `seventh.reach`, `seventh.cost`) and re-checked by
computation
    The seventh derivation's exploration is run beside the ninth's at the
    same bound on terms and the same rounds: the ninth's results asserting
    nothing with `s`, read as their `r` parts, with their rounds and their
    shortest-sequence counts, must be exactly the seventh's; and so must the
    results asserting nothing with `r`, read as their `s` parts (the exchange
    of the relations); every result's exchange must be a result at the same
    round with the same count (`compare_with_seventh`); the seventh's cost of
    the `r` part plus the `s` total must be the round of every result and the
    sum of the two parts' costs must exceed it by the terms (`write_run`);
    the seventh's criterion on either part must agree with the ninth's on
    every pair (`write_reach`); the seventh's single-relation counts must be
    the counts of results asserting nothing with `s` (`write_counts`).

Cited from the eighth derivation (`eighth.explore`, `eighth.state`,
`eighth.cost`, `eighth.changes`, `eighth.orbits`, `eighth.reach`) and
re-checked by computation
    The eighth derivation's exploration is run beside the ninth's at the same
    bound on terms with `EIGHTH_ROUNDS_FEWER` rounds fewer, from each of its
    two beginnings and under each of its two readings: under any rewriting,
    the ninth's results with a term whose eighth-seed cost is within the
    eighth's rounds must be exactly the eighth's results, each at the round
    its eighth-seed cost formula gives; with the names kept, the eighth's
    results with the names forgotten must be results of the ninth, and every
    result of the ninth with a term and small enough size must be among them
    (`compare_with_eighth`); the eighth's criterion must agree with the
    ninth's on every pair of results with a term (`write_reach`); the
    eighth's count of changes making some `xrx` or `xsx` asserted must equal
    the ninth's (`write_run`); the eighth's counts by destroyed givens must
    add up to the ninth's counts, and the ninth's counts must exceed the
    product of the seventh's for two or more terms and equal it for fewer
    (`write_counts`).  This is the computed form of rule 5 for the seventh's
    and eighth's computed claims.

Everything about the two dials turned at once — the empty beginning with two
relations, the cost as the size and its two readings per relation, the
exchange of the relations, the one-term binomial, the two-term closed form
with eight multiplicities, the count of results whose relations agree — is
written afresh.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from eighth.changes import attempt_counts as attempt_counts_eighth
from eighth.explore import explore as explore_eighth
from eighth.orbits import counts_upto as counts_upto_eighth
from eighth.state import given as given_eighth
from seventh.explore import count_shortest_sequences as count_shortest_sequences_seventh
from seventh.explore import explore as explore_seventh
from seventh.state import empty as empty_seventh
from seventh.state import forget_canonical_forms as forget_part_forms
from xry.evidence import _write_csv, _write_json, alternative, compare_evidence, write_manifest
from xry.state import Sameness

from ninth.changes import Kind, attempt_counts, first_changes, perform
from ninth.cost import GIVEN_SIZE, cost, cost_eighth, part_costs, raises_by_one
from ninth.explore import (
    Attempt,
    Exploration,
    count_shortest_sequences,
    cycle,
    explore,
    order,
    performed,
    sequences_exact,
)
from ninth.follows import verdicts
from ninth.invariants import fewest_classes, lowered, size_moves_by_one, term_stays
from ninth.orbits import (
    agreeing_count,
    agreeing_within,
    count_results,
    count_results_part,
    counts_within,
    layer_counts,
    one_term_sequences,
    product_count,
    two_term_count,
    two_term_round_count,
)
from ninth.reach import reach_graph, reachable, reachable_eighth, reachable_in_graph, reachable_on_part
from ninth.state import (
    DState,
    MState,
    added,
    canonical,
    empty,
    forget_canonical_forms,
    forget_names,
    has_term,
    swap,
    written,
)

__all__ = [
    "EIGHTH_ROUNDS_FEWER",
    "ChangeCheck",
    "Plan",
    "added_rows",
    "attempt_record",
    "check_changes",
    "compare_evidence",
    "compare_with_eighth",
    "compare_with_seventh",
    "eighth_ok",
    "frontier_rows",
    "one_term_binomial",
    "result_rows",
    "run_tag",
    "seventh_ok",
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
    bound on terms are infinite, as under the fourth to eighth seeds).  One
    beginning and one reading, so three explorations in all: the main one
    (`bound` terms, `rounds` rounds), a deeper one with fewer terms
    (`deep_bound`, `deep_rounds`), and one with two terms and
    `two_term_rounds` rounds.  `census_bound`, `census_rounds` give a larger
    run at which only counts are recorded; `census_bound = 0` turns it off.
    Reachability is tested among the results of (`reach_bound`,
    `reach_rounds`) along the changes among the results of (`reach_bound`,
    `reach_rounds + reach_extra`).  The seventh derivation's exploration runs
    beside each run at the same bound and rounds; the eighth derivation's
    explorations run with `EIGHTH_ROUNDS_FEWER` rounds fewer, so that every
    eighth result lies within the ninth's rounds (its size is at most its
    eighth-seed cost plus four).
    """

    bound: int = 5
    rounds: int = 8
    census_bound: int = 6
    census_rounds: int = 8
    deep_bound: int = 3
    deep_rounds: int = 9
    two_term_rounds: int = 12
    log_bound: int = 2
    log_rounds: int = 3
    reach_bound: int = 3
    reach_rounds: int = 5
    reach_extra: int = 2
    layers_upto: int = 14
    count_upto: int = 5
    count_total_upto: int = 10

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


#: The eighth derivation's explorations run with this many rounds fewer than the ninth's.
EIGHTH_ROUNDS_FEWER = 4


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change and its outcome, with the relation of an assertion.

    `makes_some_xrx_asserted` and `makes_some_xsx_asserted` say whether the
    outcome asserts some loop in that relation while the state asserts none
    (a property of the outcome, as under the sixth to eighth seeds).
    """
    return {
        "state": rec.state.key(),
        "written": written(rec.state),
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
    """`given.json`: the empty beginning, its one change, what it reaches, the eighth's beginnings seen from here."""
    start = empty()
    first = first_changes()
    expl = explore(start, bound=2, rounds=1, keep_log=True)
    one = DState.of(1, [], [])
    ara = DState.of(1, [(0, 0)], [])
    asa = DState.of(1, [], [(0, 0)])
    arb = DState.of(2, [(0, 1)], [])
    arb_bra = DState.of(2, [(0, 1), (1, 0)], [])
    arb_asb = DState.of(2, [(0, 1)], [(0, 1)])
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
        "cost_of_ara_once": cost(ara),
        "cost_of_asa_once": cost(asa),
        "asa_is_the_exchange_of_ara": swap(ara) == asa,
        "the_eighth_seeds_beginnings_seen_from_here": {
            alternative(False): {"state": written(arb), "cost_here": cost(arb), "cost_under_the_eighth_seed": cost_eighth(arb, False)},
            alternative(True): {"state": written(arb_bra), "cost_here": cost(arb_bra), "cost_under_the_eighth_seed": cost_eighth(arb_bra, True)},
        },
        "arb_with_asb": {"state": written(arb_asb), "cost_here": cost(arb_asb), "cost_under_the_eighth_seed": cost_eighth(arb_asb, False)},
        "the_one_term_state_under_the_eighth_seed": {
            alternative(False): cost_eighth(one, False),
            alternative(True): cost_eighth(one, True),
        },
        "ara_once_under_the_eighth_seed": cost_eighth(ara, False),
        "asa_once_under_the_eighth_seed": cost_eighth(asa, False),
        "the_exchange_keeps_the_cost_here_and_not_under_the_eighth_seed": cost(ara) == cost(asa) and cost_eighth(ara, False) != cost_eighth(asa, False),
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "of_which_add_a_term": sum(1 for c in first if c.kind is Kind.ADD_TERM),
        "attempts_not_performed": sum(1 for rec in expl.log if rec.outcome is None and not rec.beyond),
    }


def result_rows(expl: Exploration, sequences: dict[DState, int], seventh_sequences: dict[MState, int]) -> list[list[object]]:
    """One row per result."""
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        terms, assertions = added(state)
        attempts, additions, xrx, xsx = attempt_counts(state)
        cost_r, cost_s = part_costs(state)
        exchanged = canonical(swap(state))
        rows.append(
            [
                state.key(),
                written(state),
                state.n,
                state.m,
                state.total_r,
                state.total_s,
                state.distinct,
                state.most,
                terms,
                assertions,
                expl.depth[state],
                cost(state),
                cost_r,
                cost_s,
                fewest_classes(state.r_part()) if state.legal_r else "",
                fewest_classes(state.s_part()) if state.legal_s else "",
                attempts,
                additions,
                xrx,
                xsx,
                int(expl.depth[state] < expl.rounds),
                sequences[state],
                int(sequences_exact(expl, state)),
                int(has_term(state)),
                int(reachable(state, expl.start)),
                int(reachable(expl.start, state)),
                int(state.nothing_in_s),
                int(state.total_r == 0),
                int(state.r == state.s),
                int(exchanged == state),
                exchanged.key(),
                int(state.simple),
                int(state.legal_r),
                int(state.legal_s),
                int(has_term(state)),
                "" if not has_term(state) else cost_eighth(state, False),
                "" if not has_term(state) else cost_eighth(state, True),
                seventh_sequences.get(state.r_part(), "") if state.nothing_in_s else "",
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
    "seventh_seed_cost_of_the_r_part",
    "seventh_seed_cost_of_the_s_part",
    "fewest_classes_r",
    "fewest_classes_s",
    "changes",
    "of_which_additions",
    "changes_making_some_xrx_asserted",
    "changes_making_some_xsx_asserted",
    "changes_attempted",
    "shortest_sequences_of_changes",
    "shortest_sequences_exact_within_bound",
    "has_a_term",
    "reaches_what_is_given",
    "reached_from_what_is_given",
    "nothing_in_s",
    "nothing_in_r",
    "relations_agree_everywhere",
    "unchanged_by_the_exchange",
    "exchange",
    "asserts_nothing_twice",
    "asserts_no_xrx",
    "asserts_no_xsx",
    "is_a_result_of_the_eighth_seed",
    "eighth_seed_cost_without_bra",
    "eighth_seed_cost_with_bra",
    "shortest_sequences_seventh_seed",
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
    per_state: dict[DState, int] = {}
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
    xsx_made: int


def check_changes(expl: Exploration) -> ChangeCheck:
    """On every change within the bound: the cost rises by at most one, and more.

    Checks that the outcome's cost is at most the state's plus one; that the
    size moves by exactly one; that the rule saying which changes raise the
    cost by exactly one (the additions, of either relation) agrees with the
    outcome; that a state with a term leaves a state with a term; and counts
    the changes on which the earlier derivations' kept counts and properties
    fall, the changes whose outcome is of a lower, the same, or the next
    round, and the changes that make some `xrx` or some `xsx` asserted.
    """
    checked = 0
    over: list[str] = []
    stuck: list[str] = []
    wrong: list[str] = []
    lost: list[str] = []
    lowering: dict[str, int] = {}
    raised = kept = fell = made_r = made_s = 0
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
        made_r += state.legal_r and not raw.legal_r
        made_s += state.legal_s and not raw.legal_s
        step = expl.depth[out] - expl.depth[state]
        if step > 0:
            raised += 1
        elif step == 0:
            kept += 1
        else:
            fell += 1
    return ChangeCheck(
        checked,
        tuple(over),
        tuple(stuck),
        tuple(wrong),
        tuple(lost),
        dict(sorted(lowering.items())),
        raised,
        kept,
        fell,
        made_r,
        made_s,
    )


def one_term_binomial(expl: Exploration, sequences: dict[DState, int]) -> bool:
    """Every result with one term, `ara` `p` times and `asa` `q` times, is reached by `C(p + q, p)` shortest sequences."""
    return all(sequences[s] == one_term_sequences(s.r[0], s.s[0]) for s in expl.depth if s.n == 1)


def compare_with_seventh(expl: Exploration, sequences: dict[DState, int]) -> dict[str, object]:
    """The ninth's results asserting nothing with one relation against the seventh derivation's exploration.

    The seventh's exploration runs at the ninth's bound and rounds.  The
    ninth's results asserting nothing with `s`, read as their `r` parts, with
    their rounds, must be exactly the seventh's results with their rounds,
    and the numbers of shortest sequences must agree (a shortest sequence to
    such a result never touches `s`); by the exchange of the relations, the
    same must hold of the results asserting nothing with `r` read as their
    `s` parts.  Every result's exchange must be a result at the same round
    with the same number of shortest sequences.
    """
    seventh = explore_seventh(empty_seventh(), expl.bound, expl.rounds)
    seventh_sequences = count_shortest_sequences_seventh(seventh)
    only_r = {s.r_part(): r for s, r in expl.depth.items() if s.nothing_in_s}
    only_s = {s.s_part(): r for s, r in expl.depth.items() if s.total_r == 0}
    r_rounds_agree = only_r == seventh.depth
    s_rounds_agree = only_s == seventh.depth
    r_sequences_agree = r_rounds_agree and all(sequences[s] == seventh_sequences[s.r_part()] for s in expl.depth if s.nothing_in_s)
    s_sequences_agree = s_rounds_agree and all(sequences[s] == seventh_sequences[s.s_part()] for s in expl.depth if s.total_r == 0)
    exchanges = {s: canonical(swap(s)) for s in expl.depth}
    exchange_is_a_result = all(e in expl.depth for e in exchanges.values())
    exchange_keeps_round_and_count = exchange_is_a_result and all(
        expl.depth[e] == expl.depth[s] and sequences[e] == sequences[s] for s, e in exchanges.items()
    )
    return {
        "seventh_results": len(seventh.depth),
        "results_asserting_nothing_with_s": len(only_r),
        "results_asserting_nothing_with_r": len(only_s),
        "results_asserting_nothing_with_s_are_the_seventh_results_at_the_same_rounds": r_rounds_agree,
        "results_asserting_nothing_with_r_are_the_seventh_results_at_the_same_rounds": s_rounds_agree,
        "same_shortest_sequence_counts_as_seventh_on_nothing_in_s": r_sequences_agree,
        "same_shortest_sequence_counts_as_seventh_on_nothing_in_r": s_sequences_agree,
        "every_exchange_is_a_result": exchange_is_a_result,
        "every_exchange_has_the_same_round_and_sequence_count": exchange_keeps_round_and_count,
        "results_unchanged_by_the_exchange": sum(1 for s, e in exchanges.items() if e == s),
    }


def seventh_ok(block: dict[str, object]) -> bool:
    """Every comparison with the seventh derivation passes."""
    return bool(
        block["results_asserting_nothing_with_s_are_the_seventh_results_at_the_same_rounds"]
        and block["results_asserting_nothing_with_r_are_the_seventh_results_at_the_same_rounds"]
        and block["same_shortest_sequence_counts_as_seventh_on_nothing_in_s"]
        and block["same_shortest_sequence_counts_as_seventh_on_nothing_in_r"]
        and block["every_exchange_is_a_result"]
        and block["every_exchange_has_the_same_round_and_sequence_count"]
    )


def compare_with_eighth(expl: Exploration, bra: bool) -> dict[str, object]:
    """The ninth's results with a term against the eighth derivation's exploration.

    The eighth's explorations (from `arb` alone or with `bra`, under any
    rewriting and with the names kept) are run at the ninth's bound on terms
    with `EIGHTH_ROUNDS_FEWER` rounds fewer, so every eighth result lies
    within the ninth's rounds.  Under any rewriting: the ninth's results with
    a term whose eighth-seed cost is within the eighth's rounds must be
    exactly the eighth's results, each at the round its eighth-seed cost
    gives.  With the names kept: the eighth's results with their names
    forgotten must all be results of the ninth, and every result of the
    ninth with a term and size at most the eighth's rounds minus the largest
    destroyed givens (one without `bra`, two with) must be among them.
    """
    if expl.bound < 2:
        raise ValueError("the eighth seed's beginnings have two terms")
    eighth_rounds = max(expl.rounds - EIGHTH_ROUNDS_FEWER, 0)
    free = explore_eighth(given_eighth(bra, Sameness.FREE), expl.bound, eighth_rounds)
    ours = {s for s in expl.depth if has_term(s) and cost_eighth(s, bra) <= eighth_rounds}
    same_results = ours == set(free.depth)
    rounds_agree = all(free.depth[s] == cost_eighth(s, bra) for s in ours if s in free.depth)
    anchored = explore_eighth(given_eighth(bra, Sameness.ANCHORED), expl.bound, eighth_rounds)
    forgotten = {canonical(forget_names(s)) for s in anchored.depth}
    small = {s for s in expl.depth if has_term(s) and s.size + (2 if bra else 1) <= eighth_rounds}
    return {
        "eighth_rounds": eighth_rounds,
        "eighth_results_any_rewriting": len(free.depth),
        "results_with_a_term_within_the_eighth_rounds": len(ours),
        "same_results_as_eighth_derivation_any_rewriting": same_results,
        "eighth_round_is_its_cost_formula_on_every_shared_result": rounds_agree,
        "eighth_results_names_kept": len(anchored.depth),
        "eighth_results_names_forgotten": len(forgotten),
        "eighth_results_names_forgotten_are_results": forgotten <= set(expl.depth),
        "results_with_a_term_of_small_size": len(small),
        "results_with_a_term_of_small_size_are_eighth_results_names_forgotten": small <= forgotten,
        "results_where_the_eighth_cost_equals_the_cost": sum(1 for s in expl.depth if has_term(s) and cost_eighth(s, bra) == cost(s)),
        "results_where_the_eighth_cost_is_below_the_cost": sum(1 for s in expl.depth if has_term(s) and cost_eighth(s, bra) < cost(s)),
    }


def eighth_ok(block: dict[str, object]) -> bool:
    """Every comparison with the eighth derivation passes."""
    return bool(
        block["same_results_as_eighth_derivation_any_rewriting"]
        and block["eighth_round_is_its_cost_formula_on_every_shared_result"]
        and block["eighth_results_names_forgotten_are_results"]
        and block["results_with_a_term_of_small_size_are_eighth_results_names_forgotten"]
    )


def _by_terms_total(expl: Exploration) -> dict[str, int]:
    """Explored results by (terms, total multiplicity of both relations), as text keys."""
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
    seventh = compare_with_seventh(expl, sequences)
    seventh_sequences = count_shortest_sequences_seventh(explore_seventh(empty_seventh(), bound, rounds))

    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, sequences, seventh_sequences))
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
    legal_r_per_round = [0] * (rounds + 1)
    only_r_per_round = [0] * (rounds + 1)
    only_s_per_round = [0] * (rounds + 1)
    agreeing_per_round = [0] * (rounds + 1)
    for state, r in expl.depth.items():
        legal_r_per_round[r] += state.legal_r
        only_r_per_round[r] += state.nothing_in_s
        only_s_per_round[r] += state.total_r == 0
        agreeing_per_round[r] += state.r == state.s
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
                legal_r_per_round[r],
                only_r_per_round[r],
                only_s_per_round[r],
                agreeing_per_round[r],
                sum(agreeing_count(n, r - n) for n in range(min(bound, r) + 1)),
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
            "of_which_making_some_xsx_asserted",
            "new_results_asserting_no_xrx",
            "new_results_asserting_nothing_with_s",
            "new_results_asserting_nothing_with_r",
            "new_results_with_the_relations_agreeing",
            "new_results_with_the_relations_agreeing_by_closed_form",
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
    part_mismatches = [s.key() for s in expl.depth if part_costs(s)[0] + s.total_s != cost(s) or part_costs(s)[1] + s.total_r != cost(s)]
    part_sums_off = [s.key() for s in expl.depth if sum(part_costs(s)) != cost(s) + s.n]
    # A result of round r has at most r terms, so rounds 0 .. N are complete within N terms.
    within_bound_layers = min(len(exact) - 1, bound, rounds)
    entries: dict[DState, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s, r in expl.depth.items() if s.n == bound and r < rounds}
    one_each = set(entries) == full and all(c == 1 for c in entries.values())
    edges = check_changes(expl)
    tried = [s for s, r in expl.depth.items() if r < rounds]
    awaiting = expl.awaiting
    two_term_closed = expl.new_per_round == [two_term_round_count(r) for r in range(rounds + 1)] if bound == 2 else None
    round_one = [s for s, r in expl.depth.items() if r == 1]
    agreeing_total = sum(agreeing_per_round)
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_asserting_some_xrx": sum(1 for s in expl.depth if not s.legal_r),
        "results_asserting_some_xsx": sum(1 for s in expl.depth if not s.legal_s),
        "results_with_a_term": sum(1 for s in expl.depth if has_term(s)),
        "results_asserting_nothing_with_s": sum(only_r_per_round),
        "results_asserting_nothing_with_r": sum(only_s_per_round),
        "results_with_the_relations_agreeing": agreeing_total,
        "relations_agreeing_equal_closed_form": agreeing_total == agreeing_within(bound, rounds),
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": _by_terms_total(expl) == counts_within(bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "cost_is_the_seventh_cost_of_either_part_plus_the_other_total": not part_mismatches,
        "cost_part_mismatches": part_mismatches,
        "sum_of_the_part_costs_exceeds_the_cost_by_the_terms": not part_sums_off,
        "part_sum_mismatches": part_sums_off,
        "rounds_agreeing_with_unbounded_formula": [expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)],
        "two_term_rounds_equal_closed_form": two_term_closed,
        "the_first_round_is_the_one_term_state_alone": round_one == [DState.of(1, [], [])] if rounds >= 1 else None,
        "attempts_equal_formula": expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried),
        "additions_attempted": sum(attempt_counts(s)[1] for s in tried),
        "xrx_making_equal_eighth_formula": expl.xrx_per_round[-1] == sum(attempt_counts_eighth(s)[1] for s in tried),
        "xsx_making_equal_eighth_formula": expl.xsx_per_round[-1] == sum(attempt_counts_eighth(s)[2] for s in tried),
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
        "one_term_results_follow_the_binomial": one_term_binomial(expl, sequences),
        "one_term_results_with_more_than_one_shortest_sequence": sum(1 for s in expl.depth if s.n == 1 and sequences[s] > 1),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "results_reached_from_what_is_given": sum(1 for s in expl.depth if reachable(expl.start, s)),
        "seventh_derivation": seventh,
        "eighth_derivation": {alternative(bra): compare_with_eighth(expl, bra) for bra in (False, True)},
        "statements_tested": len(found),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results, completeness, cost formula, the seventh's and the eighth's.

    No per-result file is written; the frontier is counted, not exported.
    """
    expl = explore(empty(), bound, rounds)
    sequences = count_shortest_sequences(expl)
    by_terms: dict[int, int] = {}
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s) != r]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_asserting_some_xrx": sum(1 for s in expl.depth if not s.legal_r),
        "results_asserting_nothing_with_s": sum(1 for s in expl.depth if s.nothing_in_s),
        "last_round_with_a_new_result": expl.last_new_round,
        "changes_attempted": expl.attempts_per_round[-1],
        "of_which_making_some_xrx_asserted": expl.xrx_per_round[-1],
        "of_which_making_some_xsx_asserted": expl.xsx_per_round[-1],
        "explored_equals_independent_count": _by_terms_total(expl) == counts_within(bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "one_term_results_follow_the_binomial": one_term_binomial(expl, sequences),
        "frontier_states": len({leave.state for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
        "results_of_the_last_round_whose_changes_await": len(expl.awaiting),
        "seventh_derivation": compare_with_seventh(expl, sequences),
        "eighth_derivation": {alternative(bra): compare_with_eighth(expl, bra) for bra in (False, True)},
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
    the comparison with the seventh derivation's criterion on each part
    (every pair) and with the eighth derivation's criterion on the pairs of
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
    seventh_disagreements: list[str] = []
    eighth_disagreements: list[str] = []
    reached_by: dict[DState, int] = {s: 0 for s in states}
    reaches: dict[DState, int] = {}
    found_counts: dict[DState, int] = {}
    ordered = mutual = 0
    eighth_pairs = eighth_reachable = 0
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
            if reachable_on_part(s, t, "r") != here or reachable_on_part(s, t, "s") != here:
                seventh_disagreements.append(f"{s.key()} -> {t.key()}")
            if has_term(s) and has_term(t):
                eighth_pairs += 1
                before = reachable_eighth(s, t)
                eighth_reachable += before
                if before != here:
                    eighth_disagreements.append(f"{s.key()} -> {t.key()}")
        reaches[s] = here_count
        ordered += here_count
    rows: list[list[object]] = [
        [
            s.key(),
            written(s),
            expl.depth[s],
            int(has_term(s)),
            int(s.legal_r),
            int(s.legal_s),
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
            "asserts_no_xsx",
            "results_it_reaches",
            "results_reaching_it",
            "results_it_reaches_by_search",
            "criterion_agrees_with_search",
            "reaches_what_is_given",
            "is_a_result_of_the_eighth_seed",
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
        "results_asserting_some_xrx": sum(1 for s in states if not s.legal_r),
        "results_asserting_some_xsx": sum(1 for s in states if not s.legal_s),
        "criterion_agrees_with_search": not disagreements,
        "disagreements": disagreements,
        "seventh_criterion_on_either_part_agrees_on_every_pair": not seventh_disagreements,
        "seventh_criterion_disagreements": seventh_disagreements,
        "ordered_pairs_of_results_with_a_term": eighth_pairs,
        "of_which_reachable_under_the_eighth_seed": eighth_reachable,
        "eighth_criterion_agrees_on_results_with_a_term": not eighth_disagreements,
        "eighth_criterion_disagreements": eighth_disagreements,
        "results_that_reach_what_is_given": sum(1 for s in states if reachable(s, expl.start)),
    }


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and total multiplicity, by independent count.

    All results (every well-formed two-relation state, the empty one
    included) up to rewriting, beside the seventh derivation's
    single-relation counts (the results asserting nothing with `s`), their
    product (which the two-relation count equals for at most one term and
    exceeds from two terms on: the rewriting acts on both relations at
    once), the results whose two relations agree everywhere, and, with two
    terms, the closed form.  The eighth derivation's counts by destroyed
    givens (either beginning, any rewriting) must add up to these counts for
    every `n ≥ 1`.
    """
    rows: list[list[object]] = []
    totals: list[int] = []
    degree = plan.count_total_upto
    closed_form_mismatches: list[str] = []
    eighth_add_up = True
    product_equals_below_two = True
    count_exceeds_product_from_two = True
    for n in range(plan.count_upto + 1):
        every = count_results(n, degree)
        single = count_results_part(n, degree)
        prod = product_count(n, degree)
        totals.append(sum(every))
        if n >= 1:
            for bra in (False, True):
                eighth_add_up = eighth_add_up and counts_upto_eighth(Sameness.FREE, bra, n, degree) == every
        if n <= 1:
            product_equals_below_two = product_equals_below_two and every == prod
        else:
            count_exceeds_product_from_two = count_exceeds_product_from_two and all(e >= p for e, p in zip(every, prod)) and any(e > p for e, p in zip(every, prod))
        for t in range(degree + 1):
            closed = two_term_count(t) if n == 2 else ""
            if n == 2 and closed != every[t]:
                closed_form_mismatches.append(f"2/{t}")
            rows.append([n, t, every[t], single[t], prod[t], agreeing_count(n, t), closed])
    _write_csv(
        out / "counts.csv",
        (
            "terms",
            "total_multiplicity",
            "results",
            "seventh seed results (one relation; the results asserting nothing with s)",
            "product of the seventh seed counts",
            "results whose relations agree everywhere",
            "results by the two-term closed form",
        ),
        rows,
    )
    return {
        "totals_by_terms": totals,
        "two_term_closed_form_mismatches": closed_form_mismatches,
        "eighth_counts_by_destroyed_givens_add_up_to_these": eighth_add_up,
        "product_equals_count_for_at_most_one_term": product_equals_below_two,
        "count_exceeds_product_for_two_or_more_terms": count_exceeds_product_from_two,
    }


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
            "eighth_derivation_rounds_fewer": EIGHTH_ROUNDS_FEWER,
            "size_of_what_is_given": GIVEN_SIZE,
        },
        "given": write_given(out),
        "independent_counts": write_counts(out, plan),
    }
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan)
        forget_canonical_forms()
        forget_part_forms()
    summary["runs"] = runs
    summary["reachability"] = write_reach(out, plan)
    summary["attempts_in_full_log"] = write_log(out, plan)
    census: dict[str, object] = {}
    if plan.census_bound > plan.bound:
        census[run_tag(plan.census_bound, plan.census_rounds)] = write_census(plan.census_bound, plan.census_rounds)
        forget_canonical_forms()
        forget_part_forms()
    summary["census"] = census
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
