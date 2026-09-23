"""Writes `evidence/sixteenth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_sixteenth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on the record.

Cited from the ninth derivation (`ninth.explore`, `ninth.orbits`, `ninth.reach`)
and re-checked by computation
    The ninth's exploration is run beside the sixteenth's at the same bound
    on terms and the same rounds: the sixteenth's results with an empty
    record, read as ninth states, with their rounds and their
    shortest-sequence counts, must be exactly the ninth's
    (`compare_with_ninth`) — a real comparison, since the sixteenth explores
    a larger space; the ninth's orbit count must be the record-free part of
    the sixteenth's count (`write_counts`); the ninth's criterion must admit
    every pair the sixteenth's admits and be refuted on some pair the
    sixteenth's refuses (`write_reach`).

Cited from the fourteenth derivation (`fourteenth.leftover`) and re-checked by
computation
    The leftover writing of every change of the four kinds within the bound
    must be the fourteenth's (`check_records`, field
    `writing_not_the_fourteenth`).

Everything about the feedback — the record in the state, the admission, the
potential as the cost, the mass that never falls, the carrying criterion, the
count with a third factor, the two unchosen readings — is written afresh.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ninth.explore import count_shortest_sequences as count_shortest_sequences_ninth
from ninth.explore import explore as explore_ninth
from ninth.orbits import count_results as count_results_ninth
from ninth.state import empty
from ninth.state import forget_canonical_forms as forget_ninth_forms
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from sixteenth.changes import Change16, Kind, attempt_counts16, changes16, first_changes16, perform16
from sixteenth.cost import cost16, cost_ninth, diag_mass, mass
from sixteenth.explore import (
    Attempt16,
    Exploration16,
    attempt16,
    count_shortest_sequences16,
    cycle16,
    explore16,
    order16,
    performed16,
    returns_in_two,
    sequences_exact16,
)
from sixteenth.follows import change_verdicts, verdicts16
from sixteenth.invariants import RecordCheck, check_records
from sixteenth.leftover import admissible, leftover_of16
from sixteenth.orbits import (
    count_results16,
    counts_within16,
    layer_counts16,
    ninth_part,
    one_term_round_count,
    product_count16,
    two_term_round_count16,
)
from sixteenth.reach import (
    mass_ok,
    reach_graph16,
    reachable16,
    reachable_in_graph16,
    reachable_ninth,
)
from sixteenth.state import (
    RState,
    Reading,
    add_assertion16,
    admit16,
    canonical16,
    empty16,
    forget_canonical_forms16,
    has_term16,
    remove16,
    swap16,
    written16,
)

__all__ = [
    "Plan",
    "attempt_record",
    "compare_evidence",
    "compare_with_ninth",
    "ninth_ok",
    "record_summary",
    "records_ok",
    "result_rows",
    "run_tag",
    "write_all",
    "write_alternatives",
    "write_counts",
    "write_given",
    "write_log",
    "write_reach",
    "write_run",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Every exploration is bounded in terms and in rounds: three of them
    (`bound`/`rounds`, `wide_bound`/`wide_rounds`, two terms with
    `two_term_rounds`), a full attempt log at (`log_bound`, `log_rounds`),
    reachability by search among the results of (`reach_bound`,
    `reach_rounds`) along the changes among those of `reach_extra` more
    rounds, the two unchosen readings at (`alt_bound`, `alt_rounds`) with
    their own reachability search at `alt_reach_rounds` (+ `alt_reach_extra`),
    and the independent counts up to `count_upto` terms and weight
    `count_weight_upto`.
    """

    bound: int = 3
    rounds: int = 8
    wide_bound: int = 4
    wide_rounds: int = 7
    two_term_rounds: int = 10
    log_bound: int = 2
    log_rounds: int = 3
    reach_bound: int = 3
    reach_rounds: int = 5
    reach_extra: int = 2
    alt_bound: int = 2
    alt_rounds: int = 6
    alt_reach_rounds: int = 5
    alt_reach_extra: int = 3
    layers_upto: int = 10
    count_upto: int = 4
    count_weight_upto: int = 8

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the explorations written."""
        return ((self.bound, self.rounds), (self.wide_bound, self.wide_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def attempt_record(rec: Attempt16, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change, what it leaves, whether that may be admitted, its outcome."""
    return {
        "state": rec.state.key(),
        "written": written16(rec.state),
        "round": round_,
        "change": rec.change.written(rec.state),
        "kind": rec.change.kind.value,
        "relation": rec.change.rel or None,
        "admits_a_leftover": rec.change.admits,
        "adds": list(rec.change.additions),
        "leftover": rec.leftover.written(),
        "leftover_kind": rec.leftover.kind,
        "leftover_admissible_on_the_outcome": None if rec.outcome is None else admissible(rec.leftover, rec.outcome),
        "performed": True,
        "outcome": None if rec.outcome is None else rec.outcome.key(),
        "beyond_bound": rec.beyond,
    }


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the empty beginning, its one change, and the witnesses of the paper's headline claims."""
    start = empty16()
    first = first_changes16()
    rec = attempt16(start, first[0], bound=2)
    one = RState.of(1, [])
    ara = RState.of(1, [(0, 0)])
    remove_ara = Change16(Kind.REMOVE, "r", 0, 0)
    left = perform16(ara, remove_ara)
    back = admit16(left, "r", 0, 0)
    crossed = admit16(left, "s", 0, 0)
    direct = add_assertion16(left, "s", 0, 0)
    asa = RState.of(1, [], [(0, 0)])
    # The fourteenth's witness: `arb` and `asb` both once; a removal in either relation leaves `aℓb`.
    two_both = RState.of(2, [(0, 1)], [(0, 1)])
    left_r = remove16(two_both, "r", 0, 1)
    left_s = remove16(two_both, "s", 0, 1)
    writing_r = leftover_of16(two_both, Change16(Kind.REMOVE, "r", 0, 1))
    writing_s = leftover_of16(two_both, Change16(Kind.REMOVE, "s", 0, 1))
    r_into_s = admit16(left_r, "s", 0, 1)
    # The unchosen set reading: the identity fails when the pair was recorded already.
    ara_recorded = RState.of(1, [(0, 0)], [], [(0, 0)])
    set_left = remove16(ara_recorded, "r", 0, 0, Reading.SET)
    set_back = admit16(set_left, "r", 0, 0)
    count_left = remove16(ara_recorded, "r", 0, 0)
    count_back = admit16(count_left, "r", 0, 0)
    record_raised = [
        c.written(s)
        for s in (one, ara, two_both, left)
        for c in changes16(s)
        if c.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION) and not c.admits and perform16(s, c).record_total != s.record_total
    ]
    one_cycle = cycle16(one)
    ara_cycle = cycle16(ara)
    doc: dict[str, object] = {
        "state": written16(start),
        "potential": cost16(start),
        "changes": [c.written(start) for c in first],
        "the_first_change_can_only_add_a_term": [c.kind.value for c in first] == [Kind.ADD_TERM.value],
        "leftover_of_the_first_change": rec.leftover.written(),
        "outcome_of_the_first_change": None if rec.outcome is None else written16(rec.outcome),
        "reaches_itself_in_two_changes": returns_in_two(start),
        "same_relation": {
            "start": written16(ara),
            "after_removing_ara": written16(left),
            "leftover_recorded": left.recorded(0, 0),
            "after_admitting_into_r": written16(back),
            "is_the_identity": back == ara,
            "potential_of_the_start": cost16(ara),
            "potential_after_removing": cost16(left),
        },
        "other_relation": {
            "after_admitting_into_s": written16(crossed),
            "differs_from_the_start": canonical16(crossed) != canonical16(ara),
            "after_adding_asa_directly": written16(direct),
            "differs_from_the_direct_addition": canonical16(crossed) != canonical16(direct),
            "its_ninth_state_is_asa": canonical16(crossed) == canonical16(asa),
            "potential_of_asa": cost16(asa),
            "potential_of_the_direct_addition": cost16(direct),
        },
        "the_fourteenth_witness": {
            "state": written16(two_both),
            "leftover_of_removing_arb": writing_r.written(),
            "leftover_of_removing_asb": writing_s.written(),
            "the_two_leftovers_agree": writing_r == writing_s,
            "leftover_of_removing_arb_admitted_into_s": written16(r_into_s),
            "both_removals_are_changes": (left_r.n, left_s.n) == (2, 2),
        },
        "mass": {
            "ara_reaches_the_one_term_state_under_the_ninth_criterion": reachable_ninth(ara, one),
            "ara_reaches_the_one_term_state_here": reachable16(ara, one),
            "the_one_term_state_reaches_ara": reachable16(one, ara),
            "mass_of_ara": mass(ara),
            "mass_of_the_one_term_state": mass(one),
            "mass_condition_from_ara_to_the_one_term_state": mass_ok(ara, one),
        },
        "admission_costs_three": {
            "potential_of_ara": cost16(ara),
            "ninth_cost_of_ara": cost_ninth(ara),
            "potential_of_ara_with_its_leftover_recorded": cost16(ara_recorded),
            "route_by_admission_add_term_add_remove_admit": [cost16(s) for s in (start, one, ara, left, back)],
        },
        "cycles": {
            "one_term_state": None if one_cycle is None else [one_cycle[0].written(one), one_cycle[1].written(perform16(one, one_cycle[0]))],
            "ara": None if ara_cycle is None else [ara_cycle[0].written(ara), ara_cycle[1].written(perform16(ara, ara_cycle[0]))],
            "the_ninth_add_then_remove_on_ara_returns_to": written16(perform16(perform16(ara, Change16(Kind.ADD_ASSERTION, "r", 0, 0)), remove_ara)),
            "the_ninth_add_then_remove_is_a_cycle_here": perform16(perform16(ara, Change16(Kind.ADD_ASSERTION, "r", 0, 0)), remove_ara) == ara,
        },
        "set_reading": {
            "start": written16(ara_recorded),
            "after_removing_and_admitting_under_the_set_reading": written16(set_back),
            "is_the_identity_under_the_set_reading": set_back == ara_recorded,
            "after_removing_and_admitting_under_the_count_reading": written16(count_back),
            "is_the_identity_under_the_count_reading": count_back == ara_recorded,
        },
        "direct_additions_that_change_the_record": record_raised,
        "exchange_keeps_the_record": swap16(left).record == left.record,
    }
    _write_json(out / "given.json", doc)
    same = doc["same_relation"]
    other = doc["other_relation"]
    witness = doc["the_fourteenth_witness"]
    mass_block = doc["mass"]
    set_block = doc["set_reading"]
    assert isinstance(same, dict) and isinstance(other, dict) and isinstance(witness, dict)
    assert isinstance(mass_block, dict) and isinstance(set_block, dict)
    return {
        "changes_on_the_empty_state": len(first),
        "of_which_add_a_term": sum(1 for c in first if c.kind is Kind.ADD_TERM),
        "same_relation_is_the_identity": bool(same["is_the_identity"]),
        "other_relation_is_new": bool(other["differs_from_the_start"]) and bool(other["differs_from_the_direct_addition"]),
        "leftover_of_r_admitted_into_s": bool(witness["the_two_leftovers_agree"]),
        "ninth_criterion_fails_on_ara": bool(mass_block["ara_reaches_the_one_term_state_under_the_ninth_criterion"]) and not bool(mass_block["ara_reaches_the_one_term_state_here"]),
        "set_reading_breaks_the_identity": not bool(set_block["is_the_identity_under_the_set_reading"]),
        "direct_additions_that_change_the_record": len(record_raised),
    }


def result_rows(expl: Exploration16, sequences: dict[RState, int]) -> list[list[object]]:
    """One row per result."""
    rows: list[list[object]] = []
    for rs in sorted(expl.depth, key=lambda s: (expl.depth[s], order16(s))):
        attempts, direct, admissions = attempt_counts16(rs)
        exchanged = canonical16(swap16(rs))
        rows.append(
            [
                rs.key(),
                written16(rs),
                rs.n,
                rs.state.m,
                rs.state.total_r,
                rs.state.total_s,
                rs.record_total,
                rs.record.distinct,
                rs.n,
                rs.state.m,
                rs.record_total,
                expl.depth[rs],
                cost16(rs),
                cost_ninth(rs),
                mass(rs),
                diag_mass(rs),
                attempts,
                direct,
                admissions,
                int(expl.depth[rs] < expl.rounds),
                sequences[rs],
                int(sequences_exact16(expl, rs)),
                int(has_term16(rs)),
                int(rs.record_empty),
                int(reachable16(rs, expl.start)),
                int(reachable16(expl.start, rs)),
                int(returns_in_two(rs)),
                int(exchanged == rs),
                exchanged.key(),
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
    "leftovers_recorded",
    "pairs_recorded",
    "terms_added_to_given",
    "assertions_added_to_given",
    "leftovers_added_to_given",
    "round_first_reached",
    "fewest_changes_by_formula",
    "ninth_seed_cost_of_the_state",
    "mass",
    "diagonal_mass",
    "changes",
    "of_which_direct_additions",
    "of_which_admissions",
    "changes_attempted",
    "shortest_sequences_of_changes",
    "shortest_sequences_exact_within_bound",
    "has_a_term",
    "nothing_recorded",
    "reaches_what_is_given",
    "reached_from_what_is_given",
    "has_a_two_change_cycle",
    "unchanged_by_the_exchange",
    "exchange",
)


def frontier_rows(expl: Exploration16) -> list[list[object]]:
    """One row per frontier state, with how many of its attempts leave the bound on terms."""
    per_state: dict[RState, int] = {}
    for leave in expl.frontier:
        per_state[leave.state] = per_state.get(leave.state, 0) + 1
    return [[rs.key(), written16(rs), expl.depth[rs], per_state[rs]] for rs in sorted(per_state, key=order16)]


def compare_with_ninth(expl: Exploration16, sequences: dict[RState, int]) -> dict[str, object]:
    """The sixteenth's results with an empty record against the ninth's exploration at the same bound.

    The results with an empty record, read as ninth states, with their rounds
    and their shortest-sequence counts, must be exactly the ninth's.  This is
    not an identity: the sixteenth explores a larger space along more
    changes, and a removal never leads back into the empty-record results.
    """
    ninth = explore_ninth(empty(), expl.bound, expl.rounds)
    ninth_sequences = count_shortest_sequences_ninth(ninth)
    ours = {rs.state: r for rs, r in expl.depth.items() if rs.record_empty}
    ours_sequences = {rs.state: sequences[rs] for rs in expl.depth if rs.record_empty}
    extra = sorted((s.key() for s in set(ours) - set(ninth.depth)), key=str)
    missing = sorted((s.key() for s in set(ninth.depth) - set(ours)), key=str)
    round_disagreements = [s.key() for s in ninth.depth if s in ours and ours[s] != ninth.depth[s]]
    seq_disagreements = [s.key() for s in ninth.depth if s in ours and ours_sequences[s] != ninth_sequences[s]]
    return {
        "ninth_results": len(ninth.depth),
        "results_with_an_empty_record": len(ours),
        "results_with_a_record": len(expl.depth) - len(ours),
        "empty_record_results_are_the_ninth_results": ours == ninth.depth,
        "extra_results": extra,
        "missing_results": missing,
        "round_disagreements": round_disagreements,
        "sequence_disagreements": seq_disagreements,
    }


def ninth_ok(block: dict[str, object]) -> bool:
    """The comparison with the ninth has no disagreement."""
    return bool(
        block["empty_record_results_are_the_ninth_results"]
        and not block["extra_results"]
        and not block["missing_results"]
        and not block["round_disagreements"]
        and not block["sequence_disagreements"]
    )


def record_summary(edges: RecordCheck) -> dict[str, object]:
    """The record check as a JSON object.  Disagreement lists empty on correct code."""
    return {
        "checked": edges.checked,
        "raised": edges.raised,
        "lowered": edges.lowered,
        "admissions": edges.admissions,
        "removals": edges.removals,
        "potential_not_moved_by_one": list(edges.potential_not_moved_by_one),
        "direction_mismatch": list(edges.direction_mismatch),
        "mass_fell": list(edges.mass_fell),
        "diagonal_mass_fell": list(edges.diagonal_mass_fell),
        "same_relation_not_identity": list(edges.same_relation_not_identity),
        "other_relation_same_as_start": list(edges.other_relation_same_as_start),
        "other_relation_same_as_direct": list(edges.other_relation_same_as_direct),
        "admission_left_something": list(edges.admission_left_something),
        "writing_not_the_fourteenth": list(edges.writing_not_the_fourteenth),
        "unadmitted_asserted": list(edges.unadmitted_asserted),
        "admissions_not_recorded": list(edges.admissions_not_recorded),
        "round_not_potential": list(edges.round_not_potential),
    }


def records_ok(block: dict[str, object]) -> bool:
    """The record check of one run has no disagreement."""
    lists = [v for v in block.values() if isinstance(v, list)]
    return len(lists) == 12 and all(not v for v in lists)


def _by_terms_weight(expl: Exploration16) -> dict[str, int]:
    """Explored results by (terms, weight = round − terms), as text keys."""
    out: dict[str, int] = {}
    for rs, r in expl.depth.items():
        key = f"{rs.n}/{r - rs.n}"
        out[key] = out.get(key, 0) + 1
    return out


def write_run(out: Path, bound: int, rounds: int, plan: Plan) -> dict[str, object]:
    """All files of one exploration (`bound` terms, `rounds` rounds); returns its summary."""
    tag = run_tag(bound, rounds)
    expl = explore16(empty16(), bound, rounds)
    sequences = count_shortest_sequences16(expl)
    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, sequences))
    _write_csv(
        out / f"frontier_{tag}.csv",
        ("state", "written", "round_first_reached", "leaves_by_the_change"),
        frontier_rows(expl),
    )
    exact = layer_counts16(min(plan.layers_upto, rounds))
    ninth = explore_ninth(empty(), bound, rounds)
    empty_record_per_round = [0] * (rounds + 1)
    one_term_per_round = [0] * (rounds + 1)
    for rs, r in expl.depth.items():
        empty_record_per_round[r] += rs.record_empty
        one_term_per_round[r] += rs.n == 1
    so_far = 0
    round_rows: list[list[object]] = []
    one_term_mismatches: list[int] = []
    two_term_mismatches: list[int] = []
    for r in range(rounds + 1):
        so_far += expl.new_per_round[r]
        closed_one = one_term_round_count(r)
        if closed_one != one_term_per_round[r]:
            one_term_mismatches.append(r)
        closed_two: int | str = ""
        if bound == 2:
            closed_two = two_term_round_count16(r)
            if closed_two != expl.new_per_round[r]:
                two_term_mismatches.append(r)
        round_rows.append(
            [
                r,
                expl.new_per_round[r],
                so_far,
                expl.attempts_per_round[r],
                expl.admissions_per_round[r],
                empty_record_per_round[r],
                ninth.new_per_round[r],
                one_term_per_round[r],
                closed_one,
                exact[r] if r < len(exact) else "",
                closed_two,
            ]
        )
    _write_csv(
        out / f"rounds_{tag}.csv",
        (
            "round",
            "new_results_within_bound",
            "results_so_far_within_bound",
            "changes_attempted_so_far",
            "of_which_admissions",
            "new_results_with_an_empty_record",
            "new_results_of_the_ninth_seed_within_bound",
            "new_results_with_one_term",
            "new_results_with_one_term_by_closed_form",
            "new_results_without_bound_by_the_series",
            "new_results_with_at_most_two_terms_by_the_series",
        ),
        round_rows,
    )
    found = verdicts16(expl)
    _write_csv(
        out / f"follows_{tag}.csv",
        ("statement", "wording", "in_what_is_given", "first_holds", "round", "first_fails", "round_"),
        [
            [
                v.statement,
                v.wording,
                int(v.in_given),
                "" if v.holds_at is None else written16(v.holds_at),
                "" if v.holds_round is None else v.holds_round,
                "" if v.fails_at is None else written16(v.fails_at),
                "" if v.fails_round is None else v.fails_round,
            ]
            for v in found
        ],
    )
    changes_found = change_verdicts(expl)
    by_terms: dict[int, int] = {}
    for rs in expl.depth:
        by_terms[rs.n] = by_terms.get(rs.n, 0) + 1
    edges = check_records(expl)
    tried = [s for s, r in expl.depth.items() if r < rounds]
    entries: dict[RState, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s, r in expl.depth.items() if s.n == bound and r < rounds}
    one_each = set(entries) == full and all(c == 1 for c in entries.values())
    within_bound_layers = min(len(exact) - 1, bound, rounds)
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_with_a_term": sum(1 for s in expl.depth if has_term16(s)),
        "results_with_an_empty_record": sum(empty_record_per_round),
        "results_with_a_record": len(expl.depth) - sum(empty_record_per_round),
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": _by_terms_weight(expl) == counts_within16(bound, rounds),
        "rounds_agreeing_with_unbounded_series": [expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)],
        "one_term_rounds_equal_closed_form": not one_term_mismatches,
        "one_term_closed_form_mismatches": one_term_mismatches,
        "two_term_rounds_equal_the_series": (not two_term_mismatches) if bound == 2 else None,
        "the_first_round_is_the_one_term_state_alone": [s for s, r in expl.depth.items() if r == 1] == [RState.of(1, [])] if rounds >= 1 else None,
        "attempts_equal_formula": expl.attempts_per_round[-1] == sum(attempt_counts16(s)[0] for s in tried),
        "admissions_attempted": expl.admissions_per_round[-1],
        "admissions_equal_formula": expl.admissions_per_round[-1] == sum(attempt_counts16(s)[2] for s in tried),
        "frontier_states": len(entries),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_per_state_with_N_terms": one_each,
        "results_of_the_last_round_whose_changes_await": len(expl.awaiting),
        "changes_awaiting": sum(attempt_counts16(s)[0] for s in expl.awaiting),
        "records": record_summary(edges),
        "results_with_a_two_change_cycle": sum(1 for s in expl.depth if returns_in_two(s)),
        "shortest_sequences_total": sum(sequences.values()),
        "results_reached_by_one_shortest_sequence": sum(1 for c in sequences.values() if c == 1),
        "results_with_exact_sequence_count": sum(1 for s in expl.depth if sequences_exact16(expl, s)),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable16(s, expl.start)),
        "results_reached_from_what_is_given": sum(1 for s in expl.depth if reachable16(expl.start, s)),
        "ninth_derivation": compare_with_ninth(expl, sequences),
        "statements_tested": len(found),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
        "change_statements_holding_of_every_change": [v.name for v in changes_found if v.follows],
        "change_statements_that_do_not_follow": [v.name for v in changes_found if v.holds_at is not None and v.fails_at is not None],
    }


def write_log(out: Path, plan: Plan) -> int:
    """The full attempt log of a small exploration (`plan.log_bound` terms, `plan.log_rounds` rounds)."""
    expl = explore16(empty16(), plan.log_bound, plan.log_rounds, keep_log=True)
    tag = run_tag(plan.log_bound, plan.log_rounds)
    path = out / f"attempts_{tag}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in expl.log:
            line = attempt_record(rec, expl.depth[rec.state] + 1)
            handle.write(json.dumps(line, sort_keys=True, ensure_ascii=True) + "\n")
    return len(expl.log)


def write_reach(out: Path, plan: Plan) -> dict[str, object]:
    """`reach_{tag}.csv`: what each result reaches, by the carrying criterion and by search.

    Every ordered pair of results of (`reach_bound`, `reach_rounds`) is
    tested both ways; the search follows the changes among the results of
    `reach_extra` more rounds.  The ninth's criterion (a term decides) is
    compared on every pair: it must admit every pair the sixteenth's admits,
    and the pairs it admits and the sixteenth's refuses are counted, as are
    the pairs the two mass invariants alone would admit and the criterion
    refuses.
    """
    bound, rounds = plan.reach_bound, plan.reach_rounds
    start = empty16()
    expl = explore16(start, bound, rounds)
    wide = explore16(start, bound, rounds + plan.reach_extra)
    graph = reach_graph16(wide)
    states = sorted(expl.depth, key=lambda s: (expl.depth[s], order16(s)))
    inside = set(states)
    disagreements: list[str] = []
    ninth_refuses_what_we_admit: list[str] = []
    reached_by: dict[RState, int] = {s: 0 for s in states}
    reaches: dict[RState, int] = {}
    found_counts: dict[RState, int] = {}
    ordered = mutual = ninth_admits = ninth_only = invariants_only = 0
    for s in states:
        found = reachable_in_graph16(graph, s) & inside
        found_counts[s] = len(found)
        here_count = 0
        for t in states:
            here = reachable16(s, t)
            if here != (t in found):
                disagreements.append(f"{s.key()} -> {t.key()}")
            here_count += here
            reached_by[t] += here
            if here and reachable16(t, s):
                mutual += 1
            before = reachable_ninth(s, t)
            ninth_admits += before
            if here and not before:
                ninth_refuses_what_we_admit.append(f"{s.key()} -> {t.key()}")
            if before and not here:
                ninth_only += 1
            if mass_ok(s, t) and not here:
                invariants_only += 1
        reaches[s] = here_count
        ordered += here_count
    rows: list[list[object]] = [
        [
            s.key(),
            written16(s),
            expl.depth[s],
            int(has_term16(s)),
            int(s.record_empty),
            mass(s),
            reaches[s],
            reached_by[s],
            found_counts[s],
            int(reaches[s] == found_counts[s]),
            sum(1 for t in states if reachable_ninth(s, t)),
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
            "nothing_recorded",
            "mass",
            "results_it_reaches",
            "results_reaching_it",
            "results_it_reaches_by_search",
            "criterion_agrees_with_search",
            "results_it_reaches_under_the_ninth_criterion",
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
        "criterion_agrees_with_search": not disagreements,
        "disagreements": disagreements,
        "ordered_pairs_the_ninth_criterion_admits": ninth_admits,
        "ordered_pairs_the_ninth_admits_and_this_seed_refuses": ninth_only,
        "ordered_pairs_this_seed_admits_and_the_ninth_refuses": ninth_refuses_what_we_admit,
        "ordered_pairs_the_two_mass_invariants_admit_and_the_criterion_refuses": invariants_only,
        "results_that_reach_what_is_given": sum(1 for s in states if reachable16(s, expl.start)),
    }


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and weight, by independent count, beside the readings and the ninth."""
    rows: list[list[object]] = []
    degree = plan.count_weight_upto
    ninth_mismatches: list[str] = []
    one_term_mismatches: list[str] = []
    product_equals_below_two = True
    count_exceeds_product_from_two = True
    totals: list[int] = []
    for n in range(plan.count_upto + 1):
        every = count_results16(n, degree)
        as_set = count_results16(n, degree, Reading.SET)
        no_record, ninth = ninth_part(n, degree)
        prod = product_count16(n, degree)
        totals.append(sum(every))
        if no_record != ninth:
            ninth_mismatches.append(str(n))
        if n <= 1:
            product_equals_below_two = product_equals_below_two and every == prod
        else:
            count_exceeds_product_from_two = count_exceeds_product_from_two and all(e >= p for e, p in zip(every, prod)) and any(e > p for e, p in zip(every, prod))
        for w in range(degree + 1):
            closed = one_term_round_count(w + 1) if n == 1 else ""
            if n == 1 and closed != every[w]:
                one_term_mismatches.append(f"1/{w}")
            rows.append([n, w, every[w], as_set[w], no_record[w], ninth[w], prod[w], closed])
    _write_csv(
        out / "counts.csv",
        (
            "terms",
            "weight (both totals plus twice the record)",
            "results",
            "results with the record read as a set (C-R2)",
            "results with an empty record",
            "ninth seed results (the same weight, no record)",
            "product of the ninth count and the record count",
            "results by the one-term closed form",
        ),
        rows,
    )
    return {
        "totals_by_terms": totals,
        "empty_record_counts_are_the_ninth_counts": not ninth_mismatches,
        "empty_record_count_mismatches": ninth_mismatches,
        "one_term_closed_form_mismatches": one_term_mismatches,
        "product_equals_count_for_at_most_one_term": product_equals_below_two,
        "count_exceeds_product_for_two_or_more_terms": count_exceeds_product_from_two,
        "layers_without_bound": layer_counts16(plan.layers_upto),
        "ninth_layers_without_bound": [sum(count_results_ninth(n, k - n)[k - n] for n in range(k + 1)) for k in range(plan.layers_upto + 1)],
    }


def _alternative_reach(reading: Reading, bound: int, rounds: int, extra: int) -> dict[str, object]:
    """Under an unchosen reading, which criterion agrees with search on every ordered pair of results."""
    expl = explore16(empty16(), bound, rounds, reading=reading)
    wide = explore16(empty16(), bound, rounds + extra, reading=reading)
    graph = reach_graph16(wide)
    states = sorted(expl.depth, key=lambda s: (expl.depth[s], order16(s)))
    inside = set(states)
    ninth_disagreements = mass_disagreements = 0
    for s in states:
        found = reachable_in_graph16(graph, s) & inside
        for t in states:
            ninth_disagreements += reachable_ninth(s, t) != (t in found)
            mass_disagreements += reachable16(s, t) != (t in found)
    return {
        "results": len(states),
        "ordered_pairs": len(states) * len(states),
        "ninth_criterion_disagreements_with_search": ninth_disagreements,
        "carrying_criterion_disagreements_with_search": mass_disagreements,
    }


def write_alternatives(out: Path, plan: Plan) -> dict[str, object]:
    """`alternatives.json`: the two unchosen readings of the record, explored and compared."""
    doc: dict[str, object] = {}
    for reading in (Reading.SET, Reading.DROP):
        expl = explore16(empty16(), plan.alt_bound, plan.alt_rounds, reading=reading)
        identity_failures: list[str] = []
        for rs, change, raw, _out in performed16(expl):
            if change.kind is Kind.REMOVE and admit16(raw, change.rel, change.x, change.y) != rs:
                identity_failures.append(f"{rs.key()} {change.written(rs)}")
        round_mismatches = [rs.key() for rs, r in expl.depth.items() if r != cost16(rs)]
        independent = counts_within16(plan.alt_bound, plan.alt_rounds, reading)
        doc[reading.name.lower()] = {
            "reading": reading.value,
            "bound_on_terms": plan.alt_bound,
            "rounds": plan.alt_rounds,
            "results": len(expl.depth),
            "new_results_per_round": list(expl.new_per_round),
            "explored_equals_independent_count": _by_terms_weight(expl) == independent,
            "round_equals_potential_for_every_result": not round_mismatches,
            "round_potential_mismatches": round_mismatches[:12],
            "same_relation_identity_failures": len(identity_failures),
            "first_identity_failure": identity_failures[0] if identity_failures else None,
            "reachability": _alternative_reach(reading, plan.alt_bound, plan.alt_reach_rounds, plan.alt_reach_extra),
        }
        forget_canonical_forms16()
    chosen = explore16(empty16(), plan.alt_bound, plan.alt_rounds)
    doc["count"] = {
        "reading": Reading.COUNT.value,
        "results": len(chosen.depth),
        "new_results_per_round": list(chosen.new_per_round),
    }
    _write_json(out / "alternatives.json", doc)
    return doc


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    summary: dict[str, object] = {
        "plan": {
            "bound_on_terms": plan.bound,
            "rounds": plan.rounds,
            "wide_run_bound_on_terms": plan.wide_bound,
            "wide_run_rounds": plan.wide_rounds,
            "two_term_run_rounds": plan.two_term_rounds,
            "full_log_bound_on_terms": plan.log_bound,
            "full_log_rounds": plan.log_rounds,
            "reachability_bound_on_terms": plan.reach_bound,
            "reachability_rounds": plan.reach_rounds,
            "reachability_search_rounds": plan.reach_rounds + plan.reach_extra,
            "alternatives_bound_on_terms": plan.alt_bound,
            "alternatives_rounds": plan.alt_rounds,
            "alternatives_reachability_rounds": plan.alt_reach_rounds,
            "alternatives_reachability_search_rounds": plan.alt_reach_rounds + plan.alt_reach_extra,
            "unbounded_round_counts_upto": plan.layers_upto,
            "counts_upto_terms": plan.count_upto,
            "counts_upto_weight": plan.count_weight_upto,
        },
        "reading": "C-R1: the record is a count of unadmitted leftovers per pair, in the state; C-R2 (set) and C-R3 (drop) unchosen, kept, computed",
        "given": write_given(out),
        "independent_counts": write_counts(out, plan),
    }
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan)
        forget_canonical_forms16()
        forget_ninth_forms()
    summary["runs"] = runs
    summary["reachability"] = write_reach(out, plan)
    forget_canonical_forms16()
    summary["attempts_in_full_log"] = write_log(out, plan)
    summary["alternatives"] = write_alternatives(out, plan)
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
