"""Writes `evidence/twentythird/`: every file is a pure function of the code, so it is regenerable.

Run `python code/run_twentythird.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Every differential check of this derivation records its disagreements in one
dataclass, `RaisingCheck`; every list must be empty on correct code, and each
has an injection test (`tests/test_twentythird_evidence.py`) and a mutation in
the twenty-third panel of `ci/check_mutation_bite.py`.

Cited from the first derivation (`xry.evidence`) and re-checked (no change)
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on which changes there are or on when two states are one result.

Cited from the twenty-second derivation and re-checked (computed again)
    Its exploration (`twentysecond.explore`) is the exploration of states here
    (reading C-E); its round of every state must still be the state's size
    `n + Σ |e|` (22:D4, `plain_mismatch`), and its frontier is this seed's.
    Its reachability graph (`twentysecond.reach`) is searched for D9.

Cited from the ninth and seventh derivations and re-checked (computed again)
    The ninth's exploration of every state, grouped the same way (reading
    C-E′), must give the same results at the same rounds (`ninth_mismatch`).
    The seventh's exploration, mapped in by `of_r`, must merge (D8).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field, fields
from pathlib import Path

from ninth.changes import Change, Kind, changes, perform
from ninth.explore import explore as explore_ninth
from twentysecond.explore import performed
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from twentythird.cost import (
    cost,
    cost_closed,
    fewest,
    fewest_states,
    least_tables,
    lower_bound,
    raise_set,
    record,
    search_fewest,
    set_moves_least,
    single_moves_least,
    table_weight,
    together_free_of_opposites,
)
from twentythird.embed import (
    canonical_seventh,
    first_pair,
    read_back,
    read_back_direct,
    returns_on_mapped,
    seventh_merges,
    seventh_pair,
    smallest_none,
)
from twentythird.explore import Grouped, explore, group_depths, order, shortest_sequences
from twentythird.follows import verdicts
from twentythird.orbits import (
    counts_within,
    layer_counts,
    off_diagonal_tables,
    two_term_count,
    two_term_count_by_points,
    two_term_round_count,
)
from twentythird.reach import reachable, reached_by_search, search_graph
from twentythird.readings import cost_j3, explore_j3, generated_classes, key_j2, raise_all, steps_h1
from twentythird.state import (
    DState,
    Key,
    align,
    canonical,
    empty,
    excess_table,
    nothing_certificate,
    nothing_key,
    of_r,
    plain_cost,
    plain_of,
    plain_result,
    raise_term,
    raise_terms,
    result_key,
    same,
    sum_profile,
    swap,
    written,
)

__all__ = [
    "Plan",
    "RaisingCheck",
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
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Three explorations of states (`runs`: terms, rounds, and the ninth's
    rounds for the comparison of reading C-E′), each grouped into results; a
    full attempt log at (`log_bound`, `log_rounds`); reachability among the
    results of (`reach_bound`, `reach_rounds`); the generated sameness by
    search on two terms, `same_small` assertions per relation joined within
    `same_large`; the unchosen readings at (`readings_bound`,
    `readings_rounds`); the cost searched over `g` for results of at most
    `search_terms` terms of the first run.
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
    same_small: int = 2
    same_large: int = 6
    readings_bound: int = 2
    readings_rounds: int = 8
    search_terms: int = 3
    layers_upto: int = 7
    count_upto: int = 10
    closed_form_upto: int = 100
    witness_weight: int = 5

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
class RaisingCheck:
    """Every disagreement found by the differential checks; all lists empty on correct code."""

    round_not_cost: list[str] = field(default_factory=list)
    closed_form_mismatch: list[str] = field(default_factory=list)
    fewest_mismatch: list[str] = field(default_factory=list)
    characterization_mismatch: list[str] = field(default_factory=list)
    record_mismatch: list[str] = field(default_factory=list)
    nothing_mismatch: list[str] = field(default_factory=list)
    count_mismatch: list[str] = field(default_factory=list)
    two_term_mismatch: list[str] = field(default_factory=list)
    change_mismatch: list[str] = field(default_factory=list)
    respect_mismatch: list[str] = field(default_factory=list)
    plain_mismatch: list[str] = field(default_factory=list)
    ninth_mismatch: list[str] = field(default_factory=list)
    seventh_mismatch: list[str] = field(default_factory=list)
    read_back_mismatch: list[str] = field(default_factory=list)
    reach_mismatch: list[str] = field(default_factory=list)
    exchange_mismatch: list[str] = field(default_factory=list)
    sameness_mismatch: list[str] = field(default_factory=list)
    readings_mismatch: list[str] = field(default_factory=list)

    def clean(self) -> bool:
        """No disagreement anywhere."""
        return not any(getattr(self, f.name) for f in fields(self))

    def as_dict(self) -> dict[str, list[str]]:
        """Every list, by name."""
        return {f.name: list(getattr(self, f.name)) for f in fields(self)}


def key_text(key: Key) -> str:
    """A result's mark, written: its terms, then its normal excess table."""
    n, table = key
    return f"{n}:" + ",".join(str(e) for e in table)


def _name(grouped: Grouped, key: Key) -> str:
    return f"{key_text(key)} ({written(grouped.representative(key))})"


def outcome_key(state: DState, change: Change) -> Key:
    """The result of the outcome of `change` performed on `state`."""
    return result_key(perform(state, change))


# --- checks on one exploration ---------------------------------------------------------


def check_results(grouped: Grouped, check: RaisingCheck, search_terms: int = 0) -> None:
    """Every result: its round against its cost, the closed forms and the search; its states asserting the
    fewest against those found by raising; the characterization on every state reached; the record; the
    sums; the exchange; the independent counts and the two-term closed form."""
    for key in grouped.round_of:
        rep = grouped.representative(key)
        r = grouped.round_of[key]
        name = _name(grouped, key)
        c = cost(rep)
        if c != r:
            check.round_not_cost.append(name)
        closed = cost_closed(rep)
        if closed is not None and closed != c:
            check.closed_form_mismatch.append(f"closed form: {name}")
        if rep.n <= search_terms and rep.n + search_fewest(rep) != c:
            check.closed_form_mismatch.append(f"search: {name}")
        found = {canonical(f) for f in fewest_states(rep)}
        reached = set(grouped.fewest_members(key))
        if found != reached:
            check.fewest_mismatch.append(name)
        least = set_moves_least
        for m in grouped.members[key]:
            n = m.n
            table = excess_table(m)
            is_fewest = m in reached
            if least(n, table) != is_fewest:
                check.characterization_mismatch.append(f"sets: {m.key()}")
            if n <= 3 and single_moves_least(n, table) != least(n, table):
                check.characterization_mismatch.append(f"single terms: {m.key()}")
            if n == 2 and together_free_of_opposites(n, table) != is_fewest:
                check.characterization_mismatch.append(f"two terms: {m.key()}")
            if is_fewest and (m.n, m.total_r, m.total_s) != record(rep):
                check.record_mismatch.append(f"{name} / {m.key()}")
            if sum_profile(m) != sum_profile(rep):
                check.nothing_mismatch.append(f"sums differ within {name}: {m.key()}")
        if (nothing_certificate(rep) is None) != (key == nothing_key(rep.n)):
            check.nothing_mismatch.append(name)
        image = result_key(swap(rep))
        n, in_r, in_s = record(rep)
        if (
            image not in grouped.round_of
            or grouped.round_of[image] != r
            or len(grouped.fewest_members(image)) != len(reached)
            or record(swap(rep)) != (n, in_s, in_r)
        ):
            check.exchange_mismatch.append(name)
    explored: dict[str, int] = {}
    for key, r in grouped.round_of.items():
        label = f"{key[0]}/{r - key[0]}"
        explored[label] = explored.get(label, 0) + 1
    independent = counts_within(grouped.bound, grouped.rounds)
    for label in sorted(set(explored) | set(independent)):
        if explored.get(label, 0) != independent.get(label, 0):
            check.count_mismatch.append(f"{label}: explored {explored.get(label, 0)}, counted {independent.get(label, 0)}")
    if grouped.bound >= 2:
        per_round = [0] * (grouped.rounds + 1)
        for key, r in grouped.round_of.items():
            per_round[r] += key[0] <= 2
        for r, got in enumerate(per_round):
            if got != two_term_round_count(r):
                check.two_term_mismatch.append(f"round {r}: explored {got}, closed form {two_term_round_count(r)}")


def check_changes(grouped: Grouped, check: RaisingCheck) -> dict[str, object]:
    """Every change performed on every explored state whose changes were attempted: the cost of the result
    changes by an odd number; from a state asserting the fewest, by at most one.  Returns counts."""
    checked = from_fewest = 0
    largest_jump = 0
    moves: dict[str, int] = {}
    for state, change, _, out in performed(grouped.plain):
        checked += 1
        start = result_key(state)
        end = result_key(out)
        if end not in grouped.round_of:
            check.change_mismatch.append(f"outcome not formed: {state.key()} / {change.written(state)}")
            continue
        step = grouped.round_of[end] - grouped.round_of[start]
        if step % 2 == 0:
            check.change_mismatch.append(f"parity: {state.key()} / {change.written(state)}")
        if grouped.plain.depth[state] == grouped.round_of[start]:
            from_fewest += 1
            if step > 1:
                check.change_mismatch.append(f"from a state asserting the fewest: {state.key()} / {change.written(state)}")
        largest_jump = max(largest_jump, step)
        label = f"{change.kind.value} {step:+d}"
        moves[label] = moves.get(label, 0) + 1
    return {
        "changes_checked": checked,
        "changes_from_states_asserting_the_fewest": from_fewest,
        "largest_rise_of_the_cost_in_one_change": largest_jump,
        "how_each_kind_moves_the_cost": dict(sorted(moves.items())),
    }


def check_respect(grouped: Grouped, check: RaisingCheck, most_terms: int = 3) -> dict[str, object]:
    """Which changes respect the sameness: on results with at most `most_terms` terms, every addition of an
    assertion and every identification performed on each of the result's reached states lands on one
    result; adding a term does so only with at most one term (witnesses in `given.json`)."""
    tried = 0
    for key, members in grouped.members.items():
        n = key[0]
        if n > most_terms or len(members) < 2:
            continue
        rep = members[0]
        others = [align(m, rep) for m in members[1:]]
        for change in changes(rep):
            if change.kind is Kind.REMOVE or (change.kind is Kind.ADD_TERM and n >= 2):
                continue
            want = outcome_key(rep, change)
            for m in others:
                tried += 1
                if outcome_key(m, change) != want:
                    check.respect_mismatch.append(f"{_name(grouped, key)} / {change.written(rep)} on {m.key()}")
    return {"outcomes_compared": tried}


def compare_with_plain(grouped: Grouped, check: RaisingCheck) -> dict[str, object]:
    """The twenty-second's round of every state reached is its size; the round of its result here is at most
    that, by an even number; how many twenty-second results each result takes in."""
    merged = 0
    most = 0
    for key, members in grouped.members.items():
        r = grouped.round_of[key]
        most = max(most, len(members))
        merged += len(members) - 1
        for m in members:
            if plain_cost(m) != grouped.plain.depth[m] or (plain_cost(m) - r) % 2 or plain_cost(m) < r:
                check.plain_mismatch.append(m.key())
    return {
        "twentysecond_results_reached": len(grouped.plain.depth),
        "results_here": len(grouped.round_of),
        "twentysecond_results_merged_away": merged,
        "most_twentysecond_results_in_one_result": most,
        "results_whose_twentysecond_states_are_all_asserting_the_fewest": sum(
            1 for k, v in grouped.members.items() if len(grouped.fewest_members(k)) == len(v)
        ),
    }


def compare_with_ninth(grouped: Grouped, ninth_rounds: int, check: RaisingCheck) -> dict[str, object]:
    """Reading C-E′: the ninth's exploration of every state, grouped, against the grouping here."""
    ninth = explore_ninth(empty(), grouped.bound, ninth_rounds)
    theirs = group_depths(ninth.depth)
    ours = {k: r for k, r in grouped.round_of.items() if r <= ninth_rounds}
    if theirs != ours:
        missing = len(set(ours) - set(theirs))
        extra = len(set(theirs) - set(ours))
        check.ninth_mismatch.append(f"{missing} results missing, {extra} extra, rounds differ elsewhere")
    return {
        "ninth_rounds": ninth_rounds,
        "ninth_states_reached": len(ninth.depth),
        "results_formed_from_them": len(theirs),
        "results_here_within_those_rounds": len(ours),
    }


def compare_with_seventh(grouped: Grouped, check: RaisingCheck) -> dict[str, object]:
    """The seventh's results mapped in: they merge, the first merge is found, and the witness pairs hold."""
    merges = seventh_merges(grouped.bound, grouped.rounds)
    a, b = seventh_pair()
    c, d = first_pair()
    if canonical_seventh(a) == canonical_seventh(b) or result_key(of_r(a)) != result_key(of_r(b)):
        check.seventh_mismatch.append("the seventh pair")
    if canonical_seventh(c) == canonical_seventh(d) or result_key(of_r(c)) != result_key(of_r(d)):
        check.seventh_mismatch.append("the first seed's pair")
    if grouped.bound >= 2 and grouped.rounds >= 4 and (merges.first_merge is None or merges.first_merge_round != 4):
        check.seventh_mismatch.append("no merge of seventh results at round 4")
    first = merges.first_merge
    return {
        "seventh_results": merges.seventh_results,
        "results_here_they_map_to": merges.results_here,
        "most_seventh_results_in_one_result": merges.largest_merge,
        "first_merge": None if first is None else [first[0].written(), first[1].written()],
        "its_round": merges.first_merge_round,
    }


def check_read_back(grouped: Grouped, check: RaisingCheck) -> dict[str, object]:
    """The map back from the exploration against the map back computed from one state; its first "none"."""
    none = 0
    for key in grouped.round_of:
        rep = grouped.representative(key)
        back = read_back(grouped, key)
        direct = read_back_direct(rep)
        none += back is None
        if back != direct:
            check.read_back_mismatch.append(_name(grouped, key))
    first = smallest_none(grouped)
    if grouped.bound >= 2 and grouped.rounds >= 4 and (first is None or grouped.round_of[first] != 4 or first[0] != 2):
        check.read_back_mismatch.append("the first result answered none is not a two-term result of round 4")
    at_first_round = (
        []
        if first is None
        else [
            written(grouped.representative(k))
            for k in grouped.ordered_keys()
            if grouped.round_of[k] == grouped.round_of[first] and read_back(grouped, k) is None
        ]
    )
    return {
        "results_answered_none": none,
        "first_result_answered_none": None if first is None else written(grouped.representative(first)),
        "its_states_asserting_the_fewest": []
        if first is None
        else [written(m) for m in grouped.fewest_members(first)],
        "its_round": None if first is None else grouped.round_of[first],
        "results_answered_none_in_that_round": at_first_round,
        "on_the_twentysecond_results_mapped_in": returns_on_mapped(grouped),
    }


def check_reach(grouped: Grouped, check: RaisingCheck) -> tuple[dict[str, object], list[list[object]]]:
    """The reachability criterion against a search along the changes, on every ordered pair of results."""
    graph = search_graph(grouped)
    keys = grouped.ordered_keys()
    rows: list[list[object]] = []
    ordered = 0
    for s in keys:
        found = reached_by_search(grouped, graph, s)
        count = 0
        for t in keys:
            here = reachable(grouped.representative(s), grouped.representative(t))
            if here != (t in found):
                check.reach_mismatch.append(f"{key_text(s)} -> {key_text(t)}")
            count += here
        ordered += count
        rows.append([key_text(s), written(grouped.representative(s)), grouped.round_of[s], int(s[0] >= 1), count, len(found & set(keys))])
    return {
        "bound_on_terms": grouped.bound,
        "rounds": grouped.rounds,
        "results": len(keys),
        "ordered_pairs": len(keys) ** 2,
        "ordered_pairs_reachable": ordered,
    }, rows


def check_sameness(small: int, large: int, check: RaisingCheck) -> dict[str, object]:
    """The equivalence the seed's three clauses generate, found by search on one and two terms, against
    `result_key`."""
    out: dict[str, object] = {}
    for n in (1, 2):
        roots = generated_classes(n, small, large, steps_h1)
        by_root: dict[DState, Key] = {}
        by_key: dict[Key, DState] = {}
        for s, root in roots.items():
            k = result_key(s)
            if by_root.setdefault(root, k) != k:
                check.sameness_mismatch.append(f"joined but not the same: {s.key()}")
            if by_key.setdefault(k, root) != root:
                check.sameness_mismatch.append(f"the same but not joined: {s.key()}")
        out[f"{n}_terms"] = {"states": len(roots), "classes": len(set(roots.values())), "results": len(by_key)}
    return out


def check_readings(bound: int, rounds: int, check: RaisingCheck, sample: Grouped) -> dict[str, object]:
    """C-H2 (every term raised at once is pairs asserted together), C-J2 with raising (its mark is kept), C-J3
    with raising (rounds against its cost)."""
    for key, members in sample.members.items():
        for m in members:
            if plain_result(raise_all(m)) != plain_result(m):
                check.readings_mismatch.append(f"C-H2: {m.key()}")
            for x in range(m.n):
                if key_j2(raise_term(m, x)) != key_j2(m):
                    check.readings_mismatch.append(f"C-J2: {m.key()} raised at {x}")
    j3 = explore_j3(bound, rounds)
    for _, (r, state) in j3.items():
        if cost_j3(state) != r:
            check.readings_mismatch.append(f"C-J3: {state.key()}")
    chosen = explore(bound, rounds)
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "C-H1_results": len(chosen.round_of),
        "C-H2_results_which_are_the_twentysecond_results": len(chosen.plain.depth),
        "C-J3_with_raising_results": len(j3),
        "C-J3_with_raising_results_per_round": [sum(1 for r, _ in j3.values() if r == k) for k in range(rounds + 1)],
        "C-H1_results_per_round": [sum(1 for r in chosen.round_of.values() if r == k) for k in range(rounds + 1)],
        "C-H2_results_per_round": [
            sum(1 for r in chosen.plain.depth.values() if r == k) for k in range(rounds + 1)
        ],
    }


def audit(bound: int, rounds: int, ninth_rounds: int, small: int = 1, large: int = 3) -> RaisingCheck:
    """Every differential check at small bounds, writing nothing: the mutation gate's assay."""
    check = RaisingCheck()
    grouped = explore(bound, rounds)
    check_results(grouped, check, search_terms=3)
    check_changes(grouped, check)
    check_respect(grouped, check)
    compare_with_plain(grouped, check)
    compare_with_ninth(grouped, ninth_rounds, check)
    compare_with_seventh(grouped, check)
    check_read_back(grouped, check)
    check_reach(grouped, check)
    check_sameness(small, large, check)
    check_readings(bound, rounds, check, grouped)
    return check


# --- witnesses --------------------------------------------------------------------------


def four_term_witness(weight: int) -> DState | None:
    """The first four-term table (weight order, then fixed order) from which raising no single term, and no
    set of all terms but one, lowers the count, while raising some set does."""
    n = 4
    for w in range(1, weight + 1):
        for table in off_diagonal_tables(n, w):
            if single_moves_least(n, table) and not set_moves_least(n, table):
                return plain_of(n, table)
    return None


def _cost_after_term(k: int) -> tuple[DState, int, int]:
    """Two terms raised at `a` `k` times (the result asserting nothing), then a term added."""
    start = raise_terms(DState(2, (0,) * 4, (0,) * 4), [k, 0])
    out = perform(start, Change(Kind.ADD_TERM, "", 0, 0))
    return start, cost(start), cost(out)


def write_given(out: Path, plan: Plan) -> dict[str, object]:
    """`given.json`: the empty beginning, and the witnesses the paper cites."""
    two = DState(2, (0,) * 4, (0,) * 4)
    raised = raise_term(two, 0)
    one = DState.of(1, [], [])
    both = DState.of(1, [(0, 0)], [(0, 0)])
    three = DState.of(3, [(0, 1)], [(1, 0)])
    added_two = perform(two, Change(Kind.ADD_TERM, "", 0, 0))
    added_raised = perform(raised, Change(Kind.ADD_TERM, "", 0, 0))
    four = DState(4, (0,) * 16, (0,) * 16)
    four_raised = raise_term(four, 2)
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    tri = DState.of(3, [(0, 1), (0, 1), (1, 2), (1, 2), (2, 0), (2, 0)], [(1, 0), (2, 1), (0, 2)])
    witness = four_term_witness(plan.witness_weight)
    a, b = seventh_pair()
    c, d = first_pair()
    arb = DState.of(2, [(0, 1)])
    arb2 = of_r(a)
    loop_arc = DState.of(2, [(0, 0), (0, 1)])
    doc: dict[str, object] = {
        "state": written(empty()),
        "changes_on_the_empty_state": [c_.written(empty()) for c_ in changes(empty())],
        "in_the_twentysecond_a_state_asserting_something_is_the_result_asserting_nothing": {
            "state": written(both),
            "is_the_result_of": written(one),
            "same_twentysecond_result": plain_result(both) == plain_result(one),
        },
        "raising_a_on_two_terms": {
            "state": written(raised),
            "the_result_asserting_nothing_here": same(raised, two),
            "the_twentysecond_result_asserting_nothing": plain_result(raised) == plain_result(two),
        },
        "a_sum_that_is_not_zero": {
            "state": written(three),
            "certificate": list(nothing_certificate(three) or ()),
        },
        "adding_a_term_to_two_states_of_one_result": {
            "states": [written(two), written(raised)],
            "one_result": same(two, raised),
            "outcomes": [written(added_two), written(added_raised)],
            "one_result_after": same(added_two, added_raised),
        },
        "identifying_two_terms_in_two_states_of_one_result": {
            "states": [written(four), written(four_raised)],
            "one_result": same(four, four_raised),
            "outcomes": [written(perform(four, ident)), written(perform(four_raised, ident))],
            "one_result_after": same(perform(four, ident), perform(four_raised, ident)),
        },
        "adding_a_term_can_raise_the_cost_by_2k_plus_1": [
            {"state": written(s), "cost": c0, "cost_after_adding_a_term": c1} for s, c0, c1 in map(_cost_after_term, (1, 2, 3))
        ],
        "three_terms_the_loops_and_two_way_sums_do_not_give_the_cost": {
            "state": written(tri),
            "lower_bound_from_loops_and_two_way_sums": lower_bound(tri),
            "cost": cost(tri),
        },
        "four_terms_single_terms_do_not_find_the_fewest": None
        if witness is None
        else {
            "state": written(witness),
            "assertions": witness.m,
            "fewest": fewest(witness),
            "a_state_asserting_the_fewest": written(plain_of(4, least_tables(4, excess_table(witness))[0])),
            "raising_a_single_term_or_all_but_one_lowers_it": not single_moves_least(4, excess_table(witness)),
            "sets_that_lower_it": [
                [x for x in range(4) if (m >> x) & 1]
                for m in range(1, 15)
                if table_weight(raise_set(4, excess_table(witness), m)) < witness.m
            ],
        },
        "the_seventh_ninth_and_twentysecond_do_not_map_one_to_one": {
            "states": [a.written(), b.written()],
            "different_seventh_results": canonical_seventh(a) != canonical_seventh(b),
            "different_twentysecond_results": plain_result(of_r(a)) != plain_result(of_r(b)),
            "one_result_here": result_key(of_r(a)) == result_key(of_r(b)),
        },
        "the_first_does_not_map_one_to_one": {
            "states": [c.written(), d.written()],
            "different_in_every_writing": canonical_seventh(c) != canonical_seventh(d),
            "one_result_here": result_key(of_r(c)) == result_key(of_r(d)),
        },
        "the_map_back": {
            "on_a_b_arb": None if (m := read_back_direct(arb)) is None else written(m),
            "on_a_b_arb_bsa": None if (m2 := read_back_direct(raised)) is None else written(m2),
            "on_a_b_arb_arb": None if (m3 := read_back_direct(arb2)) is None else written(m3),
            "states_of_a_b_arb_arb_asserting_the_fewest": sorted({written(canonical(f)) for f in fewest_states(arb2)}),
            "on_a_b_ara_arb": None if (m4 := read_back_direct(loop_arc)) is None else written(m4),
            "states_of_a_b_ara_arb_asserting_the_fewest": sorted({written(canonical(f)) for f in fewest_states(loop_arc)}),
        },
        "raising_every_term_of_a_b_once": {
            "state": written(raise_all(two)),
            "same_twentysecond_result": plain_result(raise_all(two)) == plain_result(two),
        },
    }
    _write_json(out / "given.json", doc)
    return {"changes_on_the_empty_state": len(changes(empty()))}


# --- the files --------------------------------------------------------------------------


RESULT_HEADER = (
    "result",
    "written",
    "terms",
    "recorded_assertions_in_r",
    "recorded_assertions_in_s",
    "recorded_assertions",
    "round_first_reached",
    "fewest_changes_by_formula",
    "lower_bound_from_loops_and_two_way_sums",
    "states_asserting_the_fewest",
    "twentysecond_results_taken_in",
    "shortest_sequences_of_changes",
    "the_result_asserting_nothing",
    "a_sum_that_is_not_zero",
    "map_back",
    "exchange",
)


def write_run(out: Path, bound: int, rounds: int, ninth_rounds: int, plan: Plan, check: RaisingCheck) -> dict[str, object]:
    """All files of one exploration; returns its summary and fills `check`."""
    tag = run_tag(bound, rounds)
    grouped = explore(bound, rounds)
    check_results(grouped, check, search_terms=plan.search_terms if bound == plan.bound else 0)
    changes_block = check_changes(grouped, check)
    respect_block = check_respect(grouped, check) if bound == plan.bound else {}
    plain_block = compare_with_plain(grouped, check)
    ninth_block = compare_with_ninth(grouped, ninth_rounds, check)
    seventh_block = compare_with_seventh(grouped, check)
    back_block = check_read_back(grouped, check)
    sequences = shortest_sequences(grouped)
    rows: list[list[object]] = []
    for key in grouped.ordered_keys():
        rep = grouped.representative(key)
        n, in_r, in_s = record(rep)
        cert = nothing_certificate(rep)
        back = read_back(grouped, key)
        rows.append(
            [
                key_text(key),
                written(rep),
                n,
                in_r,
                in_s,
                in_r + in_s,
                grouped.round_of[key],
                cost(rep),
                lower_bound(rep),
                len(grouped.fewest_members(key)),
                len(grouped.members[key]),
                sequences[key],
                int(cert is None),
                "" if cert is None else f"{cert[0]} {' '.join(str(t) for t in cert[1])} = {cert[2]}",
                "none" if back is None else back.key(),
                key_text(result_key(swap(rep))),
            ]
        )
    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, rows)
    groups: dict[tuple[int, int], list[int]] = {}
    for key, r in grouped.round_of.items():
        groups.setdefault((key[0], r - key[0]), []).append(r)
    _write_csv(
        out / f"added_{tag}.csv",
        ("terms_added_to_given", "assertions_added_to_given", "results", "first_round", "last_round"),
        [[t, a_, len(v), min(v), max(v)] for (t, a_), v in sorted(groups.items(), key=lambda kv: (sum(kv[0]), kv[0]))],
    )
    exits: dict[DState, int] = {}
    for leave in grouped.plain.frontier:
        exits[leave.state] = exits.get(leave.state, 0) + 1
    _write_csv(
        out / f"frontier_{tag}.csv",
        ("state", "written", "its_result", "round_first_reached", "leaves_by_the_change"),
        [[s.key(), written(s), key_text(result_key(s)), grouped.plain.depth[s], exits[s]] for s in sorted(exits, key=order)],
    )
    unbounded = layer_counts(min(plan.layers_upto, rounds))
    round_rows = []
    so_far = 0
    for r in range(rounds + 1):
        new = sum(1 for v in grouped.round_of.values() if v == r)
        so_far += new
        round_rows.append(
            [
                r,
                new,
                so_far,
                grouped.plain.new_per_round[r],
                sum(1 for k, v in grouped.round_of.items() if v == r and k[0] <= 2),
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
            "new_twentysecond_results_reached",
            "new_results_with_at_most_two_terms",
            "new_results_with_at_most_two_terms_by_closed_form",
            "new_results_without_bound",
        ),
        round_rows,
    )
    found = verdicts(grouped)
    _write_csv(
        out / f"follows_{tag}.csv",
        ("statement", "wording", "first_holds", "first_fails", "first_depends_on_the_state", "results_where_it_depends"),
        [
            [
                v.statement,
                v.wording,
                "" if v.holds_at is None else written(grouped.representative(v.holds_at)),
                "" if v.fails_at is None else written(grouped.representative(v.fails_at)),
                "" if v.depends_at is None else written(grouped.representative(v.depends_at)),
                v.results_where_it_depends,
            ]
            for v in found
        ],
    )
    by_terms: dict[int, int] = {}
    for key in grouped.round_of:
        by_terms[key[0]] = by_terms.get(key[0], 0) + 1
    fewest_counts = [len(grouped.fewest_members(k)) for k in grouped.round_of]
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(grouped.round_of),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_asserting_nothing_up_to_raising": sum(1 for k in grouped.round_of if k == nothing_key(k[0])),
        "last_round_with_a_new_result": max(grouped.round_of.values()),
        "rounds_agreeing_with_unbounded_count": [
            sum(1 for k, v in grouped.round_of.items() if v == r) == unbounded[r]
            for r in range(min(len(unbounded) - 1, bound, rounds) + 1)
        ],
        "frontier_states": len(exits),
        "frontier_entries": len(grouped.plain.frontier),
        "results_whose_states_leave_the_bound": len({result_key(s) for s in exits}),
        "most_states_asserting_the_fewest": max(fewest_counts),
        "results_with_one_state_asserting_the_fewest": sum(1 for c in fewest_counts if c == 1),
        "shortest_sequences_total": sum(sequences.values()),
        "statements_tested": len(found),
        "statements_holding_in_every_result": [v.statement for v in found if v.in_every_result],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
        "statements_depending_on_the_state": [v.statement for v in found if v.depends_at is not None],
        "changes": changes_block,
        "changes_respecting_the_sameness": respect_block,
        "twentysecond_derivation": plain_block,
        "ninth_derivation": ninth_block,
        "seventh_derivation": seventh_block,
        "map_back": back_block,
    }


def write_reach(out: Path, plan: Plan, check: RaisingCheck) -> dict[str, object]:
    """`reach_{tag}.csv`: what each result reaches, by the criterion and by search."""
    grouped = explore(plan.reach_bound, plan.reach_rounds)
    block, rows = check_reach(grouped, check)
    _write_csv(
        out / f"reach_{run_tag(plan.reach_bound, plan.reach_rounds)}.csv",
        ("result", "written", "round", "has_a_term", "results_it_reaches", "results_it_reaches_by_search"),
        rows,
    )
    return block


def write_log(out: Path, plan: Plan) -> int:
    """The full attempt log of a small exploration: each outcome state, its twenty-second result, and its
    result here."""
    grouped = explore(plan.log_bound, plan.log_rounds, keep_log=True)
    path = out / f"attempts_{run_tag(plan.log_bound, plan.log_rounds)}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in grouped.plain.log:
            here = None if rec.outcome is None else result_key(rec.outcome)
            line = {
                "state": rec.state.key(),
                "written": written(rec.state),
                "its_result": key_text(result_key(rec.state)),
                "round": grouped.plain.depth[rec.state] + 1,
                "change": rec.change.written(rec.state),
                "kind": rec.change.kind.value,
                "reaches_the_state": rec.raw.key(),
                "its_twentysecond_result": None if rec.outcome is None else rec.outcome.key(),
                "its_result_here": None if here is None else key_text(here),
                "beyond_bound": rec.beyond,
            }
            handle.write(json.dumps(line, sort_keys=True, ensure_ascii=True) + "\n")
    return len(grouped.plain.log)


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms and recorded assertions, by the independent counts."""
    rows: list[list[object]] = []
    limits = {0: plan.count_upto, 1: plan.count_upto, 2: plan.count_upto, 3: plan.count_upto - 3, 4: 4, 5: 3}
    for n, upto in limits.items():
        counts = counts_within(n, n + upto)
        for t in range(upto + 1):
            c = counts.get(f"{n}/{t}", 0)
            rows.append([n, t, c, two_term_count(t) if n == 2 else "", two_term_count_by_points(t) if n == 2 else ""])
    _write_csv(
        out / "counts.csv",
        ("terms", "recorded_assertions", "results", "two_term_closed_form", "two_term_listing_of_points"),
        rows,
    )
    closed = [two_term_round_count(r) for r in range(plan.closed_form_upto + 1)]
    return {
        "results_of_each_round_with_at_most_two_terms_up_to_round_100": closed,
        "results_with_at_most_two_terms_within_100_rounds": sum(closed),
        "results_of_each_round_without_bound": layer_counts(plan.layers_upto),
    }


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    check = RaisingCheck()
    summary: dict[str, object] = {
        "plan": {
            "runs": [list(run) for run in plan.runs()],
            "full_log": [plan.log_bound, plan.log_rounds],
            "reachability": [plan.reach_bound, plan.reach_rounds],
            "generated_sameness_checked_on": [plan.same_small, plan.same_large],
            "readings": [plan.readings_bound, plan.readings_rounds],
            "cost_searched_over_g_up_to_terms": plan.search_terms,
        },
        "given": write_given(out, plan),
        "independent_counts": write_counts(out, plan),
    }
    runs: dict[str, object] = {}
    for bound, rounds, ninth_rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, ninth_rounds, plan, check)
    summary["runs"] = runs
    summary["reachability"] = write_reach(out, plan, check)
    summary["attempts_in_full_log"] = write_log(out, plan)
    summary["generated_sameness"] = check_sameness(plan.same_small, plan.same_large, check)
    readings = check_readings(plan.readings_bound, plan.readings_rounds, check, explore(plan.readings_bound, plan.readings_rounds))
    _write_json(out / "readings.json", readings)
    summary["disagreements"] = check.as_dict()
    summary["every_check_clean"] = check.clean()
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
