"""Writes `evidence/sixth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_sixth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest, `compare_evidence` and
    `alternative` do not depend on which changes there are.

Cited from the fifth derivation (`fifth.explore`, `fifth.reach`,
`fifth.cost`, `fifth.orbits`) and re-checked by computation
    The fifth derivation's exploration is run beside the sixth's at the same
    bound and rounds; the sixth's results asserting no `xrx` must be the
    fifth's results, at the same rounds, with the same numbers of shortest
    sequences on those with the names apart (FREE: with two or more terms)
    and more on the others (`compare_with_fifth`); the fifth's reachability
    criterion must agree with the sixth's on every pair of the fifth's
    results (`write_reach`); the fifth's destroyed givens must agree with the
    sixth's on every result asserting no `xrx` and on every result with the
    names apart (`write_run`); the fifth's counts by terms, total multiplicity
    and destroyed givens must be the `xrx`-free part of the sixth's
    (`write_counts`).  This is the computed form of rule 5 for the fifth's
    computed claims.

Everything about nothing being forbidden — the attempt records (every change
performed; whether the outcome asserts some `xrx`), the result rows, the
checks on changes, the counts with the diagonal pairs, the two-term closed
forms — is written afresh.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from itertools import product
from math import comb, factorial
from pathlib import Path

from fifth.cost import lost_free as lost_free_fifth
from fifth.explore import Exploration as ExplorationFifth
from fifth.explore import count_shortest_sequences as count_shortest_sequences_fifth
from fifth.explore import explore as explore_fifth
from xry.evidence import _write_csv, _write_json, alternative, compare_evidence, write_manifest
from xry.state import Sameness

from sixth.changes import Change, Kind, attempt_counts, changes, perform
from sixth.cost import cost, cost_free, cost_free_by_placement, lost, lost_fifth, lost_free, raises_by_one
from sixth.explore import Attempt, Exploration, count_shortest_sequences, cycle, explore, order, performed, sequences_exact
from sixth.follows import verdicts
from sixth.invariants import cost_rises_by_at_most_one, fewest_classes, lowered, names_stay_merged
from sixth.orbits import (
    APART_KINDS,
    NAMED_KINDS,
    count_free,
    count_named,
    counts_by_lost,
    counts_by_lost_fifth,
    layer_counts,
)
from sixth.reach import reach_graph, reachable, reachable_fifth, reachable_in_graph
from sixth.state import MState, added, canonical, forget_canonical_forms, given, largest_xrx, named_xrx, names_one_term

__all__ = [
    "ChangeCheck",
    "Plan",
    "added_rows",
    "attempt_record",
    "check_changes",
    "check_free_cost",
    "compare_evidence",
    "compare_with_fifth",
    "destroyed",
    "destroyed_fifth",
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
    bound on terms are infinite, as under the fourth and fifth seeds).  Three
    explorations per beginning and reading: the main one (`free_bound` /
    `anchored_bound` terms, `rounds` rounds), a deeper one with fewer terms
    (`deep_bound`, `deep_rounds`), and one with the given terms only and
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
    deep_rounds: int = 9
    two_term_rounds: int = 20
    log_bound: int = 2
    log_rounds: int = 3
    reach_bound: int = 3
    reach_rounds: int = 4
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


def destroyed_fifth(state: MState, bra: bool) -> int:
    """The fifth derivation's destroyed givens of the same state (its formula, as it stood)."""
    return lost_free_fifth(state, bra) if state.names is None else lost_fifth(state, bra)


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change and its outcome.

    `makes_some_xrx_asserted` says whether the outcome asserts some `xrx`
    while the state asserts none — what the fifth seed would have obstructed;
    under this seed the change is performed like any other.
    """
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
        "makes_some_xrx_asserted": rec.xrx,
        "performed": True,
        "outcome": None if rec.outcome is None else rec.outcome.key(),
        "beyond_bound": rec.beyond,
    }


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the alternatives for what is given, every attempt on them, what they reach."""
    doc: dict[str, object] = {
        "states_on_the_given_terms": "infinite: any multiplicities of arb, bra, ara, brb; the names one term with ara any number of times",
        "results_among_them": "all of them (every well-formed state with at least one term is a result)",
    }
    not_performed = 0
    xrx_off_formula = 0
    for sameness in Sameness:
        for bra in (False, True):
            start = given(bra, sameness)
            expl = explore(start, bound=3, rounds=1, keep_log=True)
            attempts, xrx = attempt_counts(start)
            not_performed += sum(1 for rec in expl.log if rec.outcome is None and not rec.beyond)
            xrx_off_formula += int(sum(1 for rec in expl.log if rec.xrx) != xrx)
            names = start.names
            one = MState.of(1, [], None if names is None else (0, 0))
            merged = perform(start, Change(Kind.IDENTIFY, 0, 1))
            twice = MState.of(2, [(0, 1), (0, 1)] + ([(1, 0)] if bra else []), names)
            empty = MState.of(2, [], names)
            loop = perform(start, Change(Kind.ADD_ASSERTION, 0, 0))
            doc[f"{sameness.value}/{alternative(bra)}"] = {
                "state": start.written(),
                "changes": attempts,
                "of_which_make_some_xrx_asserted": xrx,
                "of_which_obstructed": 0,
                "attempts": [attempt_record(rec, 1) for rec in expl.log],
                "reaches_the_other_beginning": reachable(start, given(not bra, sameness)),
                "the_other_beginning_reaches_it": reachable(given(not bra, sameness), start),
                "reaches_the_one_term_state": reachable(start, one),
                "the_one_term_state_reaches_it": reachable(one, start),
                "identifying_a_and_b_gives": merged.written(),
                "identifying_a_and_b_reaches_what_is_given_back": reachable(merged, start),
                "cost_of_identifying_a_and_b": cost(merged, bra),
                "fifth_formula_for_the_same_state": merged.size - (2 + (2 if bra else 1)) + 2 * destroyed_fifth(merged, bra),
                "reaches_arb_asserted_twice": reachable(start, twice),
                "reaches_nothing_asserted": reachable(start, empty),
                "nothing_asserted_reaches_what_is_given": reachable(empty, start),
                "adding_ara_gives": loop.written(),
                "cost_of_adding_ara": cost(loop, bra),
                "cost_of_nothing_asserted": cost(empty, bra),
                "cost_of_the_one_term_state": cost(one, bra),
            }
    _write_json(out / "given.json", doc)
    return {"attempts_not_performed": not_performed, "beginnings_whose_xrx_count_differs_from_formula": xrx_off_formula}


def result_rows(expl: Exploration, bra: bool, sequences: dict[MState, int], fifth: dict[MState, int]) -> list[list[object]]:
    """One row per result."""
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        terms, assertions = added(state)
        attempts, xrx = attempt_counts(state)
        c = cost(state, bra)
        rows.append(
            [
                state.key(),
                state.written(),
                state.n,
                state.m,
                state.distinct,
                state.most,
                largest_xrx(state),
                terms,
                assertions,
                expl.depth[state],
                "" if c is None else c,
                destroyed(state, bra),
                destroyed_fifth(state, bra),
                fewest_classes(state) if state.legal else "",
                attempts,
                xrx,
                int(expl.depth[state] < expl.rounds),
                sequences[state],
                int(sequences_exact(expl, state, bra)),
                int(reachable(state, expl.start)),
                int(names_one_term(state)),
                int(destroyed(state, bra) == 0),
                int(state.simple),
                int(state.legal),
                fifth.get(state, ""),
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
    "destroyed_givens",
    "destroyed_givens_fifth_formula",
    "fewest_classes",
    "changes",
    "changes_making_some_xrx_asserted",
    "changes_attempted",
    "shortest_sequences_of_changes",
    "shortest_sequences_exact_within_bound",
    "reaches_what_is_given",
    "names_one_term",
    "contains_what_is_given",
    "asserts_nothing_twice",
    "asserts_no_xrx",
    "shortest_sequences_fifth_seed",
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
    per_state: dict[MState, int] = {}
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


def check_changes(expl: Exploration, bra: bool) -> ChangeCheck:
    """On every change within the bound: the cost rises by at most one, and more.

    Checks that the outcome's cost is at most the state's plus one; with
    names, that the rule saying which changes raise it by exactly one agrees
    with the outcome; that names once one term stay one term; and counts the
    changes on which the earlier derivations' kept counts and properties
    fall, the changes whose outcome is of a lower, the same, or the next
    round, and the changes that make some `xrx` asserted.
    """
    checked = 0
    over: list[str] = []
    wrong: list[str] = []
    apart: list[str] = []
    lowering: dict[str, int] = {}
    raised = kept = fell = made = 0
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
        made += state.legal and not raw.legal
        step = expl.depth[out] - expl.depth[state]
        if step > 0:
            raised += 1
        elif step == 0:
            kept += 1
        else:
            fell += 1
    return ChangeCheck(checked, tuple(over), tuple(wrong), tuple(apart), dict(sorted(lowering.items())), raised, kept, fell, made)


def names_apart_or_two_terms(state: MState) -> bool:
    """The results on which the fifth's shortest-sequence counts must be the sixth's."""
    if state.names is not None:
        return not names_one_term(state)
    return state.n >= 2


def compare_with_fifth(
    expl: Exploration, fifth: ExplorationFifth, sequences: dict[MState, int], fifth_sequences: dict[MState, int]
) -> dict[str, object]:
    """The results asserting no `xrx` against the fifth derivation's exploration.

    Both explorations must have the same bound on terms and the same rounds.
    The results asserting no `xrx`, with their rounds, must be exactly the
    fifth's results with their rounds; the number of shortest sequences
    reaching each must be the fifth's on the results with the names apart
    (FREE: with two or more terms) and larger on every other one.
    """
    legal = {s: r for s, r in expl.depth.items() if s.legal}
    rounds_agree = legal == fifth.depth
    shared = [s for s in legal if s in fifth.depth]
    apart_agree = rounds_agree and all(sequences[s] == fifth_sequences[s] for s in shared if names_apart_or_two_terms(s))
    merged = [s for s in shared if not names_apart_or_two_terms(s)]
    return {
        "results_asserting_no_xrx": len(legal),
        "fifth_derivation_results": len(fifth.depth),
        "same_results_and_rounds_as_fifth_derivation": rounds_agree,
        "same_shortest_sequence_counts_on_fifth_results_with_names_apart": apart_agree,
        "fifth_results_with_the_names_one_term": len(merged),
        "fifth_results_with_more_shortest_sequences": sum(1 for s in merged if sequences[s] > fifth_sequences[s]),
        "fifth_results_with_fewer_shortest_sequences": sum(1 for s in shared if sequences[s] < fifth_sequences[s]),
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


def _c(n: int, k: int) -> int:
    """`C(n, k)`, zero when `n < k` or `n < 0`."""
    return comb(n, k) if 0 <= k <= n else 0


def two_term_round_count(bra: bool, r: int) -> int:
    """Results of round `r` with at most the given terms, names kept, in closed form.

    Without `bra`: the names apart with `arb` `1 + i` times, `bra` `j`,
    `ara` `p`, `brb` `q`, `i + j + p + q = r` (`C(r+3, 3)`); `arb` missing,
    `j + p + q = r − 1` (`C(r+1, 2)`); the one-term state with `ara` `K`
    times, of cost 2 for `K = 0` and `K` otherwise (one in every round
    `r ≥ 1`, two in round 2); the names one term with a second term, `crc`
    `K` times: `K = 0`, `C(r−1, 2)`; `K ≥ 1`, `C(r+1, 3)`.  With `bra`:
    both givens present, `C(r+3, 3)`; one missing, `2·C(r+1, 2)`; both
    missing, `r − 1` for `r ≥ 2`; the one-term state with `crc` `K` times
    (cost 3, 2, then `K − 1`: none in round 0, one in round 1, two in rounds
    2 and 3, one after); with a second term: `K = 0`, `C(r−2, 2)`; `K = 1`,
    `C(r−1, 2)`; `K ≥ 2`, `C(r+1, 3)`.
    """
    if not bra:
        one = {0: 0, 1: 1, 2: 2}.get(r, 1)
        return _c(r + 3, 3) + _c(r + 1, 2) + one + _c(r - 1, 2) + _c(r + 1, 3)
    one = {0: 0, 1: 1, 2: 2, 3: 2}.get(r, 1)
    both_missing = r - 1 if r >= 2 else 0
    return _c(r + 3, 3) + 2 * _c(r + 1, 2) + both_missing + one + _c(r - 2, 2) + _c(r - 1, 2) + _c(r + 1, 3)


def _two_term_multinomial(expl: Exploration, sequences: dict[MState, int], bra: bool) -> bool | None:
    """On two-term results with names apart: the shortest sequences are the arrangements of the cost-raising changes.

    Each given `g` contributes `M(g) − 1` additions when `M(g) ≥ 1` (an item
    repeated `M(g) − 1` times) and one removal when `M(g) = 0`; `bra` when
    not given contributes `M(b,a)` additions; `ara` and `brb` contribute
    their multiplicities.  The count is the multinomial coefficient.
    """
    if expl.start.names is None:
        return None
    for state in expl.depth:
        if state.n != 2 or state.names is None or names_one_term(state):
            continue
        a, b = state.names
        items: list[int] = []
        for x, y, is_given in ((a, b, True), (b, a, bra)):
            k = state.mult_of(x, y)
            items.append(k - 1 if is_given and k >= 1 else (1 if is_given else k))
        items += [state.mult_of(a, a), state.mult_of(b, b)]
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
    fifth = explore_fifth(start, bound, rounds)
    sequences = count_shortest_sequences(expl)
    fifth_sequences = count_shortest_sequences_fifth(fifth)

    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, bra, sequences, fifth_sequences))
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
    legal_per_round = [0] * (rounds + 1)
    merged_per_round = [0] * (rounds + 1)
    for state, r in expl.depth.items():
        legal_per_round[r] += state.legal
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
                legal_per_round[r],
                fifth.new_per_round[r],
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
            "of_which_making_some_xrx_asserted",
            "new_results_asserting_no_xrx",
            "new_results_fifth_derivation",
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
    entries: dict[MState, int] = {}
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
    fifth_lost_differs = [s for s in expl.depth if destroyed(s, bra) != destroyed_fifth(s, bra)]
    merged_with_crc = [s for s in expl.depth if names_one_term(s) and named_xrx(s) >= 1]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_by_destroyed_givens": {str(k): by_lost[k] for k in sorted(by_lost)},
        "results_asserting_some_xrx": sum(1 for s in expl.depth if not s.legal),
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": _by_lost(expl, bra) == _counted(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "rounds_agreeing_with_unbounded_formula": [
            expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)
        ],
        "two_term_rounds_equal_closed_form": two_term_closed,
        **compare_with_fifth(expl, fifth, sequences, fifth_sequences),
        "fifth_destroyed_givens_differ_on": len(fifth_lost_differs),
        "results_with_the_names_one_term_and_crc_asserted": len(merged_with_crc),
        "fifth_destroyed_givens_differ_exactly_on_those": (
            set(fifth_lost_differs) == set(merged_with_crc) if sameness is Sameness.ANCHORED else None
        ),
        "fifth_destroyed_givens_agree_on_every_result_asserting_no_xrx": all(s.legal is False or s not in fifth_lost_differs for s in expl.depth),
        "results_with_fewer_terms_or_assertions_than_given": sum(1 for s in expl.depth if min(added(s)) < 0),
        "results_with_the_names_one_term": sum(merged_per_round),
        "attempts_equal_formula": expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried),
        "xrx_making_equal_formula": expl.xrx_per_round[-1] == sum(attempt_counts(s)[1] for s in tried),
        "attempts_obstructed": 0,
        "frontier_states": len(entries),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_per_state_with_N_terms": one_each,
        "results_of_the_last_round_whose_changes_await": len(awaiting),
        "changes_awaiting": sum(attempt_counts(s)[0] for s in awaiting),
        "changes_checked": edges.checked,
        "changes_making_some_xrx_asserted": edges.xrx_made,
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
        "two_term_sequences_equal_multinomial": _two_term_multinomial(expl, sequences, bra),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_census(sameness: Sameness, bra: bool, bound: int, rounds: int) -> dict[str, object]:
    """Counts only, at a larger bound: results, completeness, cost formula, the fifth's.

    No per-result file is written; the frontier is counted, not exported.
    """
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    fifth = explore_fifth(start, bound, rounds)
    sequences = count_shortest_sequences(expl)
    fifth_sequences = count_shortest_sequences_fifth(fifth)
    by_terms: dict[int, int] = {}
    for state in expl.depth:
        by_terms[state.n] = by_terms.get(state.n, 0) + 1
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_asserting_some_xrx": sum(1 for s in expl.depth if not s.legal),
        "last_round_with_a_new_result": expl.last_new_round,
        "changes_attempted": expl.attempts_per_round[-1],
        "of_which_making_some_xrx_asserted": expl.xrx_per_round[-1],
        "explored_equals_independent_count": _by_lost(expl, bra) == _counted(sameness, bra, bound, rounds),
        "round_equals_cost_formula_for_every_result": not mismatches,
        **compare_with_fifth(expl, fifth, sequences, fifth_sequences),
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
    with the comparison with the fifth derivation's criterion on the fifth's
    results.
    """
    bound, rounds = plan.reach_bound, plan.reach_rounds
    start = given(bra, sameness)
    expl = explore(start, bound, rounds)
    fifth = explore_fifth(start, bound, rounds)
    wide = explore(start, bound, rounds + plan.reach_extra)
    graph = reach_graph(wide)
    states = sorted(expl.depth, key=lambda s: (expl.depth[s], order(s)))
    inside = set(states)
    disagreements: list[str] = []
    fifth_disagreements: list[str] = []
    reached_by: dict[MState, int] = {s: 0 for s in states}
    reaches: dict[MState, int] = {}
    found_counts: dict[MState, int] = {}
    ordered = mutual = 0
    fifth_pairs = fifth_reachable = 0
    xrx_pairs = xrx_reachable = 0
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
            if s in fifth.depth and t in fifth.depth:
                fifth_pairs += 1
                before = reachable_fifth(s, t)
                fifth_reachable += before
                if before != here:
                    fifth_disagreements.append(f"{s.key()} -> {t.key()}")
            if not s.legal or not t.legal:
                xrx_pairs += 1
                xrx_reachable += here
        reaches[s] = here_count
        ordered += here_count
    rows: list[list[object]] = [
        [
            s.key(),
            s.written(),
            expl.depth[s],
            int(names_one_term(s)),
            int(s.legal),
            reaches[s],
            reached_by[s],
            found_counts[s],
            int(reaches[s] == found_counts[s]),
            int(reachable(s, expl.start)),
            int(s in fifth.depth),
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
            "asserts_no_xrx",
            "results_it_reaches",
            "results_reaching_it",
            "results_it_reaches_by_search",
            "criterion_agrees_with_search",
            "reaches_what_is_given",
            "is_a_result_of_the_fifth_seed",
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
        "results_asserting_some_xrx": sum(1 for s in states if not s.legal),
        "criterion_agrees_with_search": not disagreements,
        "disagreements": disagreements,
        "fifth_results": len(fifth.depth),
        "ordered_pairs_of_fifth_results": fifth_pairs,
        "of_which_reachable_under_the_fifth_seed": fifth_reachable,
        "fifth_criterion_agrees_on_fifth_results": not fifth_disagreements,
        "fifth_criterion_disagreements": fifth_disagreements,
        "ordered_pairs_with_some_xrx": xrx_pairs,
        "of_which_reachable": xrx_reachable,
        "results_that_reach_what_is_given": sum(1 for s in states if reachable(s, expl.start)),
    }


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and total multiplicity, by independent count.

    All results (every well-formed state) under each reading, split by how
    the named terms stand, by the one-way property and by "nothing
    off-diagonal", beside the fifth derivation's counts of states asserting no
    `xrx`, which must be the part of these counts with every `xrx` at
    multiplicity zero.
    """
    rows: list[list[object]] = []
    totals: dict[str, list[int]] = {"free": [], "anchored": []}
    legal_is_fifth = True
    combos = [(s, b) for s in Sameness for b in (False, True)]
    degree = plan.count_total_upto
    for n in range(1, plan.count_upto + 1):
        free_all = count_free(n, degree)
        one_way = count_free(n, degree, one_way=True)
        only_diag = count_free(n, degree, off=False)
        named = count_named(n, degree)
        named_legal = count_named(n, degree, cap=0)
        totals["free"].append(sum(free_all))
        totals["anchored"].append(sum(sum(v) for v in named.values()))
        for s, b in combos:
            ours = {k: v for k, v in counts_by_lost(s, b, n, degree, cap=0).items() if any(v)}
            theirs = {k: v for k, v in counts_by_lost_fifth(s, b, n, degree).items() if any(v)}
            legal_is_fifth = legal_is_fifth and ours == theirs
        for t in range(degree + 1):
            rows.append(
                [
                    n,
                    t,
                    free_all[t],
                    one_way[t],
                    only_diag[t],
                    *(named[kind][t] for kind in NAMED_KINDS),
                    count_free(n, degree, cap=0)[t],
                    *(named_legal[kind][t] for kind in APART_KINDS),
                    named_legal["one term, crc not asserted"][t],
                ]
            )
    _write_csv(
        out / "counts.csv",
        (
            "terms",
            "total_multiplicity",
            "results free",
            "results free never both ways",
            "results free nothing off-diagonal",
            *(f"results anchored: {k}" for k in NAMED_KINDS),
            "fifth seed results free",
            *(f"fifth seed results anchored: {k}" for k in APART_KINDS),
            "fifth seed results anchored: a and b one term",
        ),
        rows,
    )
    return {"totals": totals, "fifth_counts_are_the_xrx_free_part": legal_is_fifth}


def check_free_cost(bound: int, most: int) -> tuple[int, list[str]]:
    """Compare the closed form for FREE cost with the best placement of names.

    Every state with at most `bound` terms and no multiplicity above `most`
    is compared, `xrx` multiplicities included.
    """
    checked = 0
    mismatches = []
    for bra in (False, True):
        for n in range(1, bound + 1):
            seen: set[MState] = set()
            for mult in product(range(most + 1), repeat=n * n):
                state = canonical(MState(n, mult))
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
