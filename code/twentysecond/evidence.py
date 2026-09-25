"""Writes `evidence/twentysecond/`: every file is a pure function of the code, so it is regenerable.

Run `python code/run_twentysecond.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Every differential check of this derivation records its disagreements in one
dataclass, `JointCheck`; every list must be empty on correct code, and each
has an injection test (`tests/test_twentysecond_evidence.py`) and a mutation
in the twenty-second panel of `ci/check_mutation_bite.py`.

Cited from the first derivation (`xry.evidence`) and re-checked (no change)
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on which changes there are or on when two states are one result.

Cited from the seventh and ninth derivations and re-checked (computed again)
    The seventh's exploration (`seventh.explore`) is run beside this seed's
    at the same bound and rounds: its results, read as asserting nothing with
    `s`, must be exactly the results whose plain state asserts nothing with
    `s`, at the same rounds, with the same shortest-sequence counts, and the
    map back must return each of them (`compare_with_seventh`).  The ninth's
    exploration (`ninth.explore`) is run at the same bound with its own
    rounds: every ninth result must be a result here at the round of its
    cost; the ninth results asserting no pair in both relations must be
    exactly the results here of those rounds, one each; the ninth's round
    (its size) must equal the cost here exactly on them (`compare_with_ninth`).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field, fields
from itertools import permutations
from pathlib import Path

from ninth.explore import explore as explore_ninth
from seventh.explore import count_shortest_sequences as count_shortest_sequences_seventh
from seventh.explore import explore as explore_seventh
from seventh.state import empty as empty_seventh
from seventh.state import forget_canonical_forms as forget_part_forms
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from twentysecond.changes import (
    Change,
    Kind,
    add_r_then_s,
    attempt_count,
    is_addition,
    padded_removals,
    perform,
    predicted_move,
    result_changes,
)
from twentysecond.embed import embed, read_back, smallest_none
from twentysecond.explore import Attempt, Exploration, count_shortest_sequences, explore, order, performed
from twentysecond.follows import verdicts
from twentysecond.orbits import count_results, counts_within, layer_counts, two_term_count, two_term_round_count
from twentysecond.reach import reach_graph, reachable, reachable_in_graph
from twentysecond.readings import (
    cost_j2,
    cost_j3,
    count_j3,
    explore_j2,
    explore_j3,
    padding_witness,
    round_count_j2,
)
from twentysecond.state import (
    DState,
    canonical,
    cost,
    empty,
    excess,
    forget_canonical_forms,
    is_plain,
    recorded,
    result_of,
    rewrite,
    same,
    swap,
    written,
)

__all__ = [
    "JointCheck",
    "Plan",
    "audit",
    "check_changes",
    "check_readings",
    "check_results",
    "check_sameness",
    "compare_evidence",
    "compare_with_ninth",
    "compare_with_seventh",
    "run_tag",
    "write_all",
    "write_given",
    "write_reach",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Three explorations of this seed (`runs`), each bounded in terms and in
    rounds; beside each, the seventh's exploration at the same bounds and the
    ninth's at the same bound on terms with its own rounds (`ninth_rounds`,
    at most the run's: every ninth result of round `k` costs at most `k`
    here).  A full attempt log at (`log_bound`, `log_rounds`); reachability
    among the results of (`reach_bound`, `reach_rounds`); the generated
    sameness checked on every state of at most `same_bound` terms and
    `same_total` assertions per relation; the unchosen readings at
    `readings_bound` terms.
    """

    bound: int = 5
    rounds: int = 8
    ninth_rounds: int = 8
    deep_bound: int = 3
    deep_rounds: int = 10
    deep_ninth_rounds: int = 9
    two_term_rounds: int = 24
    two_term_ninth_rounds: int = 12
    log_bound: int = 2
    log_rounds: int = 3
    reach_bound: int = 3
    reach_rounds: int = 4
    same_bound: int = 2
    same_total: int = 3
    readings_bound: int = 2
    readings_rounds: int = 8
    layers_upto: int = 14
    count_upto: int = 5
    count_total_upto: int = 10
    closed_form_upto: int = 100

    def runs(self) -> tuple[tuple[int, int, int], ...]:
        """(terms, rounds, ninth's rounds) of the explorations written."""
        return (
            (self.bound, self.rounds, self.ninth_rounds),
            (self.deep_bound, self.deep_rounds, self.deep_ninth_rounds),
            (2, self.two_term_rounds, self.two_term_ninth_rounds),
        )


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


@dataclass
class JointCheck:
    """Every disagreement found by the differential checks; all lists empty on correct code."""

    round_not_cost: list[str] = field(default_factory=list)
    cost_raised_by_more_than_one: list[str] = field(default_factory=list)
    record_move_mismatch: list[str] = field(default_factory=list)
    removal_outside: list[str] = field(default_factory=list)
    undo_failed: list[str] = field(default_factory=list)
    raising_not_addition: list[str] = field(default_factory=list)
    count_mismatch: list[str] = field(default_factory=list)
    two_term_mismatch: list[str] = field(default_factory=list)
    one_term_not_one_sequence: list[str] = field(default_factory=list)
    exchange_mismatch: list[str] = field(default_factory=list)
    seventh_mismatch: list[str] = field(default_factory=list)
    read_back_mismatch: list[str] = field(default_factory=list)
    ninth_mismatch: list[str] = field(default_factory=list)
    reach_mismatch: list[str] = field(default_factory=list)
    sameness_mismatch: list[str] = field(default_factory=list)
    readings_mismatch: list[str] = field(default_factory=list)

    def clean(self) -> bool:
        """No disagreement anywhere."""
        return not any(getattr(self, f.name) for f in fields(self))

    def as_dict(self) -> dict[str, list[str]]:
        """Every list, by name."""
        return {f.name: list(getattr(self, f.name)) for f in fields(self)}


def _name(state: DState, change: Change | None = None) -> str:
    return state.key() if change is None else f"{state.key()} / {change.written(state)}"


def one_term_asa() -> DState:
    """The one-term result asserting `asa` once."""
    return DState.of(1, [], [(0, 0)])


# --- checks on one exploration ---------------------------------------------------------


def check_results(expl: Exploration, sequences: dict[DState, int], check: JointCheck) -> None:
    """Rounds against the cost formula, counts against the orbit count and the two-term closed form,
    one-term sequences, the exchange, and undoing, on every explored result."""
    for state, r in expl.depth.items():
        if cost(state) != r:
            check.round_not_cost.append(_name(state))
        if state.n == 1 and sequences[state] != 1:
            check.one_term_not_one_sequence.append(_name(state))
        exchanged = swap(state)
        negated = all(excess(exchanged, x, y) == -excess(state, x, y) for x in range(state.n) for y in range(state.n))
        image = result_of(exchanged)
        n, in_r, in_s = recorded(state)
        kept = image in expl.depth and expl.depth[image] == r and sequences[image] == sequences[state]
        if not negated or not kept or recorded(exchanged) != (n, in_s, in_r):
            check.exchange_mismatch.append(_name(state))
        if r < expl.rounds and state.n >= 1:
            for x in range(state.n):
                for y in range(state.n):
                    if result_of(add_r_then_s(state, x, y)) != state:
                        check.undo_failed.append(f"{_name(state)} / {x}r{y} then {x}s{y}")
    explored: dict[str, int] = {}
    for state in expl.depth:
        key = f"{state.n}/{sum(recorded(state)[1:])}"
        explored[key] = explored.get(key, 0) + 1
    independent = counts_within(expl.bound, expl.rounds)
    for key in sorted(set(explored) | set(independent)):
        if explored.get(key, 0) != independent.get(key, 0):
            check.count_mismatch.append(f"{key}: explored {explored.get(key, 0)}, counted {independent.get(key, 0)}")
    if expl.bound >= 2:
        per_round = [0] * (expl.rounds + 1)
        for state, r in expl.depth.items():
            per_round[r] += state.n <= 2
        for r, got in enumerate(per_round):
            if got != two_term_round_count(r):
                check.two_term_mismatch.append(f"round {r}: explored {got}, closed form {two_term_round_count(r)}")


def check_changes(expl: Exploration, check: JointCheck) -> dict[str, object]:
    """On every change within the bound: the cost rises by at most one, the recorded counts move as the
    rule says, a change raising the round is an addition; and removals from states that are not plain
    land on an outcome of the plain state's changes (reading C-X).  Returns counts for the summary."""
    moves: dict[str, dict[str, int]] = {}
    raised = kept = fell = checked = 0
    for state, change, raw, out in performed(expl):
        checked += 1
        name = _name(state, change)
        if cost(raw) > cost(state) + 1 or out not in expl.depth:
            check.cost_raised_by_more_than_one.append(name)
            continue
        before, after = recorded(state), recorded(raw)
        move = (after[0] - before[0], after[1] + after[2] - before[1] - before[2])
        if move != predicted_move(state, change):
            check.record_move_mismatch.append(name)
        kind = change.kind.value
        moves.setdefault(kind, {})
        label = f"terms {move[0]:+d}, assertions {move[1]:+d}"
        moves[kind][label] = moves[kind].get(label, 0) + 1
        step = expl.depth[out] - expl.depth[state]
        raised += step > 0
        kept += step == 0
        fell += step < 0
        if step == 1 and not is_addition(change):
            check.raising_not_addition.append(name)
    padded_checked = 0
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[state] >= expl.rounds:
            continue
        outs = {result_of(perform(state, c)) for c in result_changes(state)}
        for padded, removal in padded_removals(state):
            padded_checked += 1
            if result_of(perform(padded, removal)) not in outs:
                check.removal_outside.append(_name(padded, removal))
    return {
        "changes_checked": checked,
        "changes_raising_the_round": raised,
        "changes_keeping_the_round": kept,
        "changes_lowering_the_round": fell,
        "how_each_kind_moves_what_is_recorded": {k: dict(sorted(v.items())) for k, v in sorted(moves.items())},
        "removals_from_states_not_plain_checked": padded_checked,
    }


def compare_with_seventh(expl: Exploration, sequences: dict[DState, int], check: JointCheck) -> dict[str, object]:
    """The seventh's results, read here, against the results whose plain state asserts nothing with `s`."""
    seventh = explore_seventh(empty_seventh(), expl.bound, expl.rounds)
    seventh_sequences = count_shortest_sequences_seventh(seventh)
    embedded = {embed(m): r for m, r in seventh.depth.items()}
    ours = {s: r for s, r in expl.depth.items() if s.total_s == 0}
    if embedded != ours:
        check.seventh_mismatch.append(f"results: {len(embedded)} seventh, {len(ours)} here asserting nothing with s")
    for m in seventh.depth:
        e = embed(m)
        if e in expl.depth and sequences[e] != seventh_sequences[m]:
            check.seventh_mismatch.append(f"shortest sequences: {m.key()}")
        if read_back(e) != m:
            check.read_back_mismatch.append(f"map back: {m.key()}")
    first = smallest_none(expl)
    if expl.rounds >= 2 and (first != one_term_asa() or expl.depth.get(first) != 2):
        check.read_back_mismatch.append("the first result answered none is not the one-term result asserting asa once")
    return {
        "seventh_results": len(seventh.depth),
        "results_whose_plain_state_asserts_nothing_with_s": len(ours),
        "results_the_map_back_answers_none_on": sum(1 for s in expl.depth if read_back(s) is None),
        "first_result_answered_none": None if first is None else written(first),
        "its_round": None if first is None else expl.depth[first],
    }


def compare_with_ninth(expl: Exploration, ninth_rounds: int, check: JointCheck) -> tuple[dict[str, object], dict[DState, int]]:
    """The ninth's results at the same bound on terms, `ninth_rounds` rounds, merged into this seed's results."""
    ninth = explore_ninth(empty(), expl.bound, ninth_rounds)
    taken: dict[DState, int] = {}
    plain_images: dict[DState, int] = {}
    size_equals_cost_off_plain = 0
    for g, k in ninth.depth.items():
        image = result_of(g)
        if image not in expl.depth or expl.depth[image] != cost(g) or cost(g) > k:
            check.ninth_mismatch.append(f"image of {g.key()}")
            continue
        taken[image] = taken.get(image, 0) + 1
        if is_plain(g):
            plain_images[image] = plain_images.get(image, 0) + 1
            if k != cost(g):
                check.ninth_mismatch.append(f"plain ninth result whose round is not its cost: {g.key()}")
        elif k == cost(g):
            size_equals_cost_off_plain += 1
    within = {s for s, r in expl.depth.items() if r <= ninth_rounds}
    if set(plain_images) != within or any(c != 1 for c in plain_images.values()):
        check.ninth_mismatch.append("the plain ninth results are not the results of those rounds, one each")
    if size_equals_cost_off_plain:
        check.ninth_mismatch.append(f"{size_equals_cost_off_plain} ninth results off the plain ones at the round of their cost")
    counts = sorted(taken.values())
    block: dict[str, object] = {
        "ninth_rounds": ninth_rounds,
        "ninth_results": len(ninth.depth),
        "ninth_results_asserting_no_pair_in_both_relations": sum(plain_images.values()),
        "results_here_within_the_ninth_rounds": len(within),
        "results_here_taking_in_more_than_one_ninth_result": sum(1 for c in counts if c > 1),
        "most_ninth_results_taken_in_by_one_result": counts[-1] if counts else 0,
        "ninth_results_merged_away": len(ninth.depth) - len(taken),
    }
    return block, taken


def check_sameness(bound: int, total: int, check: JointCheck) -> dict[str, object]:
    """The equivalence the changed sentence generates, found by joining states directly, against `same`.

    Every state with at most `bound` terms and at most `total` assertions in
    each relation is joined to each rewriting of it and to itself with one
    more pair asserted together (when that stays within `total`); the
    resulting classes must be exactly those of `same`.
    """
    states: list[DState] = []
    for n in range(bound + 1):
        cells = n * n

        def vectors(k: int, left: int) -> list[tuple[int, ...]]:
            if k == 0:
                return [()]
            return [(v, *rest) for v in range(left + 1) for rest in vectors(k - 1, left - v)]

        for in_r in vectors(cells, total):
            for in_s in vectors(cells, total):
                states.append(DState(n, in_r, in_s))
    parent = {s: s for s in states}

    def find(s: DState) -> DState:
        while parent[s] != s:
            parent[s] = parent[parent[s]]
            s = parent[s]
        return s

    def join(a: DState, b: DState) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for s in states:
        for p in permutations(range(s.n)):
            join(s, rewrite(s, p))
        for x in range(s.n):
            for y in range(s.n):
                i = x * s.n + y
                if s.total_r < total and s.total_s < total:
                    r = list(s.r)
                    t = list(s.s)
                    r[i] += 1
                    t[i] += 1
                    join(s, DState(s.n, tuple(r), tuple(t)))
    classes: dict[DState, list[DState]] = {}
    for s in states:
        classes.setdefault(find(s), []).append(s)
    for members in classes.values():
        head = members[0]
        for other in members[1:]:
            if not same(head, other):
                check.sameness_mismatch.append(f"joined but not the same: {head.key()} {other.key()}")
    by_result: dict[DState, DState] = {}
    for s in states:
        root = find(s)
        seen = by_result.setdefault(result_of(s), root)
        if seen != root:
            check.sameness_mismatch.append(f"the same but not joined: {s.key()}")
    return {"states": len(states), "classes": len(classes), "results": len(by_result)}


def check_readings(bound: int, rounds: int, check: JointCheck) -> dict[str, object]:
    """The unchosen readings C-J2 and C-J3 at a small bound: rounds against their cost formulas, counts
    against their closed form and orbit count, and the C-X witness of C-J3."""
    j2 = explore_j2(bound, rounds)
    for pair, r in j2.items():
        if cost_j2(pair) != r:
            check.readings_mismatch.append(f"C-J2 round of {pair}")
    j2_rounds = [sum(1 for r in j2.values() if r == k) for k in range(rounds + 1)]
    for k, got in enumerate(j2_rounds):
        if got != round_count_j2(k, bound):
            check.readings_mismatch.append(f"C-J2 round {k}")
    j3 = explore_j3(bound, rounds)
    for state, r in j3.items():
        if cost_j3(state) != r:
            check.readings_mismatch.append(f"C-J3 round of {state.key()}")
    explored: dict[str, int] = {}
    for state in j3:
        key = f"{state.n}/{cost_j3(state) - state.n}"
        explored[key] = explored.get(key, 0) + 1
    counted = {
        f"{n}/{t}": c for n in range(min(bound, rounds) + 1) for t, c in enumerate(count_j3(n, rounds - n)) if c
    }
    if explored != counted:
        check.readings_mismatch.append("C-J3 explored counts differ from the orbit count")
    witnesses = []
    for k in range(1, 4):
        padded, result, c = padding_witness(k)
        witnesses.append({"state": written(padded), "identified": written(result), "cost_under_the_plain_changes": c})
        if c != 1 + 2 * k or not same(padded, DState(2, (0,) * 4, (0,) * 4)):
            check.readings_mismatch.append(f"C-J3 padding witness {k}")
    chosen = explore(empty(), bound, rounds)
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "chosen_reading_results": len(chosen.depth),
        "C-J2_results": len(j2),
        "C-J2_results_per_round": j2_rounds,
        "C-J3_results": len(j3),
        "C-J3_results_per_round": [sum(1 for r in j3.values() if r == k) for k in range(rounds + 1)],
        "C-J3_under_C-X_identify_two_terms_carrying_k_pairs_asserted_together": witnesses,
    }


def check_reach(expl: Exploration, check: JointCheck) -> tuple[dict[str, object], list[list[object]]]:
    """The reachability criterion against a search along the changes, on every ordered pair of results."""
    graph = reach_graph(expl)
    states = sorted(expl.depth, key=lambda s: (expl.depth[s], order(s)))
    rows: list[list[object]] = []
    ordered = mutual = 0
    for s in states:
        found = reachable_in_graph(graph, s)
        count = 0
        for t in states:
            here = reachable(s, t)
            if here != (t in found):
                check.reach_mismatch.append(f"{s.key()} -> {t.key()}")
            count += here
            mutual += here and reachable(t, s)
        ordered += count
        rows.append([s.key(), written(s), expl.depth[s], int(s.n >= 1), count, len(found), int(count == len(found))])
    return {
        "bound_on_terms": expl.bound,
        "rounds": expl.rounds,
        "results": len(states),
        "ordered_pairs": len(states) ** 2,
        "ordered_pairs_reachable": ordered,
        "unordered_pairs_reachable_both_ways": (mutual - len(states)) // 2,
        "ordered_pairs_unreachable": len(states) ** 2 - ordered,
    }, rows


def audit(bound: int, rounds: int, ninth_rounds: int, same_bound: int = 1, same_total: int = 2) -> JointCheck:
    """Every differential check at small bounds, writing nothing: the mutation gate's assay."""
    check = JointCheck()
    expl = explore(empty(), bound, rounds)
    sequences = count_shortest_sequences(expl)
    check_results(expl, sequences, check)
    check_changes(expl, check)
    compare_with_seventh(expl, sequences, check)
    compare_with_ninth(expl, ninth_rounds, check)
    check_reach(expl, check)
    check_sameness(same_bound, same_total, check)
    check_readings(bound, rounds, check)
    return check


# --- the files --------------------------------------------------------------------------


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt: the change, the state it reaches, and that state's result with what it records."""
    move = None if rec.outcome is None else predicted_move(rec.state, rec.change)
    return {
        "result": rec.state.key(),
        "written": written(rec.state),
        "round": round_,
        "change": rec.change.written(rec.state),
        "kind": rec.change.kind.value,
        "relation": rec.change.rel or None,
        "reaches_the_state": rec.raw.key(),
        "the_state_asserts_a_pair_in_both_relations": not is_plain(rec.raw),
        "which_is_the_result": None if rec.outcome is None else rec.outcome.key(),
        "recorded_for_that_result": None if rec.outcome is None else list(recorded(rec.outcome)),
        "moves_what_is_recorded_by": None if move is None else list(move),
        "beyond_bound": rec.beyond,
    }


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the empty beginning, and the witnesses the paper cites."""
    start = empty()
    first = result_changes(start)
    one = DState.of(1, [], [])
    ara = DState.of(1, [(0, 0)], [])
    asa = one_term_asa()
    both = DState.of(1, [(0, 0)], [(0, 0)])
    removed = perform(both, Change(Kind.REMOVE, "r", 0, 0))
    added_other = perform(one, Change(Kind.ADD_ASSERTION, "s", 0, 0))
    lowered = perform(ara, Change(Kind.ADD_ASSERTION, "s", 0, 0))
    takes = []
    for c in range(1, 4):
        g = DState.of(2, [(0, 1)] * c, [(1, 0)] * c)
        o = perform(g, Change(Kind.IDENTIFY, "", 0, 1))
        takes.append({"state": written(g), "recorded": list(recorded(g)), "identified": written(o), "recorded_after": list(recorded(o))})
    arb_names_apart = DState.of(2, [(0, 1)], [], (0, 1))
    arb_names_one = DState.of(2, [(0, 1)], [], (0, 0))
    two_ara = DState.of(2, [(0, 0)], [])
    two_moved = perform(perform(two_ara, Change(Kind.ADD_ASSERTION, "r", 1, 1)), Change(Kind.ADD_ASSERTION, "s", 0, 0))
    doc: dict[str, object] = {
        "state": written(start),
        "changes": [c.written(start) for c in first],
        "the_first_change_can_only_add_a_term": [c.kind for c in first] == [Kind.ADD_TERM],
        "undoing": {
            "states": [written(one), written(ara), written(both)],
            "ninth_sizes": [one.size, ara.size, both.size],
            "the_third_is_the_first_result_here": same(one, both),
            "recorded": [list(recorded(one)), list(recorded(ara)), list(recorded(both))],
        },
        "removing_ara_from_a_state_of_the_one_term_result_is_adding_asa_to_it": {
            "state": written(both),
            "after_removing_ara": written(removed),
            "after_adding_asa_to_a": written(added_other),
            "same_result": same(removed, added_other),
        },
        "an_addition_lowers_what_is_recorded": {
            "state": written(ara),
            "after_adding_asa": written(lowered),
            "recorded_before": list(recorded(ara)),
            "recorded_after": list(recorded(lowered)),
        },
        "one_identification_takes_out_2c_assertions": takes,
        "the_ninth_does_not_map_one_to_one": {
            "states": [written(one), written(both)],
            "ninth_sizes": [one.size, both.size],
            "one_result_here": same(one, both),
        },
        "the_eighth_does_not_map_one_to_one": {
            "states": [arb_names_apart.written(), arb_names_one.written()],
            "different_eighth_states": canonical(arb_names_apart) != canonical(arb_names_one),
            "one_result_here": result_of(DState(2, arb_names_apart.r, arb_names_apart.s))
            == result_of(DState(2, arb_names_one.r, arb_names_one.s)),
        },
        "the_map_back": {
            "of_the_result_of_a_ara": None if (m := read_back(result_of(ara))) is None else m.key(),
            "of_the_result_of_a_asa": None if read_back(asa) is None else "a seventh state",
            "a_asa_costs": cost(asa),
        },
        "two_additions_on_different_pairs_that_undo_up_to_writing": {
            "state": written(two_ara),
            "after_adding_brb_then_asa": written(two_moved),
            "same_result": same(two_ara, two_moved),
            "excesses_at_the_two_loops_before_and_after": [
                [excess(two_ara, 0, 0), excess(two_ara, 1, 1)],
                [excess(two_moved, 0, 0), excess(two_moved, 1, 1)],
            ],
        },
    }
    _write_json(out / "given.json", doc)
    return {"changes_on_the_empty_state": len(first)}


RESULT_HEADER = (
    "state",
    "written",
    "terms",
    "recorded_assertions_in_r",
    "recorded_assertions_in_s",
    "recorded_assertions",
    "round_first_reached",
    "fewest_changes_by_formula",
    "changes",
    "changes_attempted",
    "shortest_sequences_of_changes",
    "has_a_term",
    "reaches_what_is_given",
    "exchange",
    "unchanged_by_the_exchange",
    "map_back_to_a_seventh_state",
    "ninth_results_taken_in",
)


def write_run(out: Path, bound: int, rounds: int, ninth_rounds: int, plan: Plan, check: JointCheck) -> dict[str, object]:
    """All files of one exploration; returns its summary and fills `check`."""
    tag = run_tag(bound, rounds)
    expl = explore(empty(), bound, rounds)
    sequences = count_shortest_sequences(expl)
    check_results(expl, sequences, check)
    changes_block = check_changes(expl, check)
    seventh = compare_with_seventh(expl, sequences, check)
    ninth, taken = compare_with_ninth(expl, ninth_rounds, check)
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        n, in_r, in_s = recorded(state)
        m = read_back(state)
        exchanged = result_of(swap(state))
        rows.append(
            [
                state.key(),
                written(state),
                n,
                in_r,
                in_s,
                in_r + in_s,
                expl.depth[state],
                cost(state),
                attempt_count(state) if state.n else 1,
                int(expl.depth[state] < expl.rounds),
                sequences[state],
                int(state.n >= 1),
                int(reachable(state, expl.start)),
                exchanged.key(),
                int(exchanged == state),
                "none" if m is None else m.key(),
                taken.get(state, 0) if expl.depth[state] <= ninth_rounds else "",
            ]
        )
    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, rows)
    groups: dict[tuple[int, int], list[int]] = {}
    for state, r in expl.depth.items():
        n, in_r, in_s = recorded(state)
        groups.setdefault((n, in_r + in_s), []).append(r)
    _write_csv(
        out / f"added_{tag}.csv",
        ("terms_added_to_given", "assertions_added_to_given", "results", "first_round", "last_round"),
        [[t, a, len(v), min(v), max(v)] for (t, a), v in sorted(groups.items(), key=lambda kv: (sum(kv[0]), kv[0]))],
    )
    exits: dict[DState, int] = {}
    for leave in expl.frontier:
        exits[leave.state] = exits.get(leave.state, 0) + 1
    _write_csv(
        out / f"frontier_{tag}.csv",
        ("state", "written", "round_first_reached", "leaves_by_the_change"),
        [[s.key(), written(s), expl.depth[s], exits[s]] for s in sorted(exits, key=order)],
    )
    unbounded = layer_counts(min(plan.layers_upto, rounds))
    round_rows = []
    so_far = 0
    for r in range(rounds + 1):
        so_far += expl.new_per_round[r]
        round_rows.append(
            [
                r,
                expl.new_per_round[r],
                so_far,
                expl.attempts_per_round[r],
                sum(1 for s, k in expl.depth.items() if k == r and s.total_s == 0),
                sum(1 for s, k in expl.depth.items() if k == r and s.n <= 2),
                two_term_round_count(r),
                unbounded[r] if r < len(unbounded) else "",
            ]
        )
    _write_csv(
        out / f"rounds_{tag}.csv",
        (
            "round",
            "new_results_within_bound",
            "results_so_far_within_bound",
            "changes_attempted_so_far",
            "new_results_the_map_back_returns",
            "new_results_with_at_most_two_terms",
            "new_results_with_at_most_two_terms_by_closed_form",
            "new_results_without_bound_by_formula",
        ),
        round_rows,
    )
    found = verdicts(expl)
    _write_csv(
        out / f"follows_{tag}.csv",
        ("statement", "wording", "first_holds", "round", "first_fails", "round_"),
        [
            [
                v.statement,
                v.wording,
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
    tried = [s for s, r in expl.depth.items() if r < rounds]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "last_round_with_a_new_result": expl.last_new_round,
        "rounds_agreeing_with_unbounded_formula": [
            expl.new_per_round[r] == unbounded[r] for r in range(min(len(unbounded) - 1, bound, rounds) + 1)
        ],
        "attempts": expl.attempts_per_round[-1],
        "attempts_equal_formula": expl.attempts_per_round[-1] == sum(attempt_count(s) if s.n else 1 for s in tried),
        "frontier_states": len(exits),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_per_state_with_N_terms": set(exits) == {s for s in tried if s.n == bound}
        and all(c == 1 for c in exits.values()),
        "results_of_the_last_round_whose_changes_await": len(expl.awaiting),
        "shortest_sequences_total": sum(sequences.values()),
        "results_reached_by_one_shortest_sequence": sum(1 for c in sequences.values() if c == 1),
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if reachable(s, expl.start)),
        "statements_tested": len(found),
        "statements_holding_in_every_result": [v.statement for v in found if v.in_every_result],
        "statements_holding_in_no_result": [v.statement for v in found if v.in_no_result],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
        "changes": changes_block,
        "seventh_derivation": seventh,
        "ninth_derivation": ninth,
    }


def write_reach(out: Path, plan: Plan, check: JointCheck) -> dict[str, object]:
    """`reach_{tag}.csv`: what each result reaches, by the criterion and by search."""
    expl = explore(empty(), plan.reach_bound, plan.reach_rounds)
    block, rows = check_reach(expl, check)
    _write_csv(
        out / f"reach_{run_tag(plan.reach_bound, plan.reach_rounds)}.csv",
        (
            "state",
            "written",
            "round",
            "has_a_term",
            "results_it_reaches",
            "results_it_reaches_by_search",
            "criterion_agrees_with_search",
        ),
        rows,
    )
    return block


def write_log(out: Path, plan: Plan) -> int:
    """The full attempt log of a small exploration."""
    expl = explore(empty(), plan.log_bound, plan.log_rounds, keep_log=True)
    path = out / f"attempts_{run_tag(plan.log_bound, plan.log_rounds)}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in expl.log:
            handle.write(json.dumps(attempt_record(rec, expl.depth[rec.state] + 1), sort_keys=True, ensure_ascii=True) + "\n")
    return len(expl.log)


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and recorded assertions, by orbit count and closed form."""
    rows: list[list[object]] = []
    totals: list[int] = []
    for n in range(plan.count_upto + 1):
        counts = count_results(n, plan.count_total_upto)
        totals.append(sum(counts))
        for t, c in enumerate(counts):
            rows.append([n, t, c, two_term_count(t) if n == 2 else "", (1 if t == 0 else 2) if n == 1 else ""])
    _write_csv(
        out / "counts.csv",
        ("terms", "recorded_assertions", "results", "results_by_the_two_term_closed_form", "results_with_one_term"),
        rows,
    )
    closed = [two_term_round_count(r) for r in range(plan.closed_form_upto + 1)]
    return {
        "totals_by_terms": totals,
        "results_of_each_round_with_at_most_two_terms_up_to_round_100": closed,
        "results_with_at_most_two_terms_within_100_rounds": sum(closed),
        "results_of_each_round_without_bound": layer_counts(plan.layers_upto),
    }


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    check = JointCheck()
    summary: dict[str, object] = {
        "plan": {
            "runs": [list(run) for run in plan.runs()],
            "full_log": [plan.log_bound, plan.log_rounds],
            "reachability": [plan.reach_bound, plan.reach_rounds],
            "generated_sameness_checked_on": [plan.same_bound, plan.same_total],
            "readings": [plan.readings_bound, plan.readings_rounds],
        },
        "given": write_given(out),
        "independent_counts": write_counts(out, plan),
    }
    runs: dict[str, object] = {}
    for bound, rounds, ninth_rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, ninth_rounds, plan, check)
        forget_canonical_forms()
        forget_part_forms()
    summary["runs"] = runs
    summary["reachability"] = write_reach(out, plan, check)
    summary["attempts_in_full_log"] = write_log(out, plan)
    summary["generated_sameness"] = check_sameness(plan.same_bound, plan.same_total, check)
    readings = check_readings(plan.readings_bound, plan.readings_rounds, check)
    _write_json(out / "readings.json", readings)
    summary["disagreements"] = check.as_dict()
    summary["every_check_clean"] = check.clean()
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
