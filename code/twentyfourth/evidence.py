"""Writes `evidence/twentyfourth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/run_twentyfourth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Every differential check of this derivation records its disagreements in one
dataclass, `FillCheck`; every list must be empty on correct code, and each has
an injection test (`tests/test_twentyfourth_evidence.py`) and a mutation in
the twenty-fourth panel of `ci/check_mutation_bite.py`.

Cited from the first derivation (`xry.evidence`) and re-checked (no change)
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on which changes there are or on when two states are one result.

Cited from the twenty-third derivation and re-checked (computed again)
    Its grouped exploration is run beside each exploration here, at the same
    bounds: its results must be this seed's results with no filled term, at
    the same rounds, with the same numbers of shortest sequences
    (`twentythird_mismatch`).  Its record is asked the task's first question
    over its own results (`record_question_mismatch`).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field, fields
from itertools import permutations
from pathlib import Path

from ninth.changes import Change, Kind
from ninth.changes import changes as changes23
from ninth.changes import perform as perform23
from twentythird.state import excess_table, normal_table, rewrite_table
from twentythird.state import result_key as key23
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from twentyfourth.changes import (
    CHOSEN,
    FILL_BALANCE,
    FILL_COUNT,
    FILL_LOOPS,
    ID_BOTH,
    ID_EITHER,
    ID_NEVER,
    Fill,
    Move,
    Reading,
    kind_of,
    moves,
    perform24,
    written,
)
from twentyfourth.cost import cost, cost_counted, potential, record23
from twentyfourth.embed import (
    compare_with_twentythird,
    forget_key,
    read_back,
    record_question,
    record_witnesses,
    smallest_none,
)
from twentyfourth.explore import Grouped, explore, performed, shortest_sequences
from twentyfourth.follows import verdicts
from twentyfourth.orbits import (
    counts_within,
    layer_counts,
    one_term_sequences,
    two_term_count,
    two_term_count_by_points,
    two_term_round_count,
)
from twentyfourth.reach import reachable, reached_by_search, search_graph
from twentyfourth.readings import generated_classes, identification_outcomes
from twentyfourth.state import (
    DState,
    FState,
    Key24,
    balance_record,
    keeping_size,
    key_balance,
    result_key,
    rewrite,
    swap,
    tell_class,
)

__all__ = [
    "FillCheck",
    "Plan",
    "align",
    "audit",
    "check_changes",
    "check_forget",
    "check_reach",
    "check_read_back",
    "check_readings",
    "check_record_question",
    "check_respect",
    "check_results",
    "check_sameness",
    "compare_evidence",
    "compare_twentythird",
    "key_text",
    "run_tag",
    "write_all",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Three explorations of states (`runs`: terms, rounds), each grouped into
    results and compared with the twenty-third's run at the same bounds; a full
    attempt log at (`log_bound`, `log_rounds`); reachability among the results
    of (`reach_bound`, `reach_rounds`) under each reading of identifying; the
    generated sameness by search on one and two terms, `same_small` assertions
    per relation joined within `same_large`; the unchosen readings at
    (`readings_bound`, `readings_rounds`).

    Two preconditions make the searches complete: the joins of the sameness
    need `same_large ≥ 3 · same_small` (two same states on two terms differ by
    raising one term at most `2 · same_small` times, 23:D1); and reachability
    by search needs `reach_bound ≥ 2` and `reach_rounds ≥ 3`, since under
    C-I2 and C-I3 a filled term is merged away through a second term, at cost
    three (paper, D12).
    """

    bound: int = 5
    rounds: int = 7
    deep_bound: int = 3
    deep_rounds: int = 9
    two_term_rounds: int = 16
    log_bound: int = 2
    log_rounds: int = 3
    reach_bound: int = 2
    reach_rounds: int = 4
    same_small: int = 1
    same_large: int = 4
    readings_bound: int = 2
    readings_rounds: int = 6
    layers_upto: int = 7
    closed_form_upto: int = 100
    points_upto: int = 8

    def __post_init__(self) -> None:
        if self.same_large < 3 * self.same_small:
            raise ValueError("the sameness search joins within at least three times its states' assertions")
        if self.reach_bound < 2 or self.reach_rounds < 3:
            raise ValueError("reachability by search needs two terms and three rounds")

    def runs(self) -> tuple[tuple[int, int], ...]:
        """(terms, rounds) of the explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


@dataclass
class FillCheck:
    """Every disagreement found by the differential checks; all lists empty on correct code."""

    round_not_cost: list[str] = field(default_factory=list)
    balance_mismatch: list[str] = field(default_factory=list)
    tell_mismatch: list[str] = field(default_factory=list)
    record_mismatch: list[str] = field(default_factory=list)
    count_mismatch: list[str] = field(default_factory=list)
    two_term_mismatch: list[str] = field(default_factory=list)
    sequences_mismatch: list[str] = field(default_factory=list)
    change_mismatch: list[str] = field(default_factory=list)
    respect_mismatch: list[str] = field(default_factory=list)
    twentythird_mismatch: list[str] = field(default_factory=list)
    read_back_mismatch: list[str] = field(default_factory=list)
    forget_mismatch: list[str] = field(default_factory=list)
    reach_mismatch: list[str] = field(default_factory=list)
    exchange_mismatch: list[str] = field(default_factory=list)
    sameness_mismatch: list[str] = field(default_factory=list)
    readings_mismatch: list[str] = field(default_factory=list)
    record_question_mismatch: list[str] = field(default_factory=list)

    def clean(self) -> bool:
        """No disagreement anywhere."""
        return not any(getattr(self, f.name) for f in fields(self))

    def as_dict(self) -> dict[str, list[str]]:
        """Every list, by name."""
        return {f.name: list(getattr(self, f.name)) for f in fields(self)}


def key_text(key: Key24) -> str:
    """A result's mark, written: its terms, its normal excess table, its filled terms."""
    n, table, fills = key
    return f"{n}:" + ",".join(str(e) for e in table) + ":" + "".join(str(k) for k in fills)


def _name(grouped: Grouped, key: Key24) -> str:
    return f"{key_text(key)} ({grouped.representative(key).written()})"


def outcome_key(state: FState, change: Move, reading: Reading = CHOSEN) -> Key24:
    """The result of the outcome of `change` performed on `state`."""
    return result_key(perform24(state, change, reading))


def align(state: FState, target: FState) -> FState:
    """A rewriting of `state` that is the same result as `target` at `target`'s writing."""
    n = state.n
    want = normal_table(n, excess_table(target.base))
    table = excess_table(state.base)
    for p in permutations(range(n)):
        moved = rewrite(state, p)
        if target.n == n and moved.fills == target.fills and normal_table(n, rewrite_table(n, table, p)) == want:
            return moved
    raise ValueError("the two states are not one result")


def class_from_key(key: Key24) -> str:
    """The told / not told class read from the mark alone (independently of `tell_class`)."""
    n, table, fills = key
    loops = [table[x * n + x] for x in range(n)]
    if any(fills[x] and loops[x] for x in range(n)):
        return "told"
    if any(loops):
        return "one filling away"
    if any(table[x * n + y] + table[y * n + x] for x in range(n) for y in range(x + 1, n)):
        return "two terms"
    return "three terms" if any(table) else "nothing"


# --- checks on one exploration ---------------------------------------------------------


def check_results(grouped: Grouped, check: FillCheck) -> None:
    """Every result: its round against the cost; the balance record of every state against the mark; the told
    class against the mark; the twenty-third's record on every state asserting the fewest; the exchange;
    every state's round against its potential; the independent counts and the two-term closed form."""
    for key in grouped.round_of:
        rep = grouped.representative(key)
        r = grouped.round_of[key]
        name = _name(grouped, key)
        if cost(rep) != r:
            check.round_not_cost.append(name)
        marked = key_balance(key)
        want = (sum(1 for _, b in marked if b), sum(1 for _, b in marked if not b))
        cls = class_from_key(key)
        for m in grouped.members[key]:
            if potential(m) != grouped.states.depth[m]:
                check.round_not_cost.append(f"state {m.key()}")
            if balance_record(m) != want:
                check.balance_mismatch.append(f"{name} / {m.key()}")
            if tell_class(m) != cls:
                check.tell_mismatch.append(f"{name} / {m.key()}")
        for m in grouped.fewest_members(key):
            if (m.n, m.base.total_r, m.base.total_s) != record23(rep.base):
                check.record_mismatch.append(f"{name} / {m.key()}")
        image = result_key(swap(rep))
        n, in_r, in_s = record23(rep.base)
        if (
            image not in grouped.round_of
            or grouped.round_of[image] != r
            or balance_record(swap(rep)) != balance_record(rep)
            or tell_class(swap(rep)) != tell_class(rep)
            or record23(swap(rep).base) != (n, in_s, in_r)
        ):
            check.exchange_mismatch.append(name)
    explored: dict[str, int] = {}
    for key, r in grouped.round_of.items():
        k = sum(1 for f in key[2] if f)
        label = f"{key[0]}/{k}/{r - key[0] - k}"
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


def check_sequences(grouped: Grouped, check: FillCheck) -> dict[str, object]:
    """Shortest sequences: on one-term results the closed form `t + 1` with the term filled, `1` without."""
    counts = shortest_sequences(grouped)
    for key, c in counts.items():
        if key[0] == 1:
            k = key[2][0]
            t = abs(key[1][0])
            if c != one_term_sequences(k, t):
                check.sequences_mismatch.append(f"{_name(grouped, key)}: {c}")
    return {
        "most_shortest_sequences_to_one_result": max(counts.values(), default=0),
        "results_reached_by_one_shortest_sequence": sum(1 for c in counts.values() if c == 1),
    }


def check_changes(grouped: Grouped, check: FillCheck) -> dict[str, object]:
    """Every change performed on every explored state whose changes were attempted: from a state asserting the
    fewest the cost rises by at most one; a filling raises it by exactly one; the move is odd except for
    identifying two filled terms (reading C-I1), which moves it by an even number; no change returns a state
    to its own result.  Returns counts."""
    checked = even = 0
    moves_seen: dict[str, int] = {}
    for state, change, raw, _ in performed(grouped.states):
        checked += 1
        start = result_key(state)
        end = result_key(raw)
        step = cost(raw) - cost(state)
        label = f"{kind_of(change)} {step:+d}"
        moves_seen[label] = moves_seen.get(label, 0) + 1
        both_filled = (
            isinstance(change, Change)
            and change.kind is Kind.IDENTIFY
            and bool(state.fills[change.x])
            and bool(state.fills[change.y])
        )
        where = f"{state.key()} / {written(change, state)}"
        if end == start:
            check.change_mismatch.append(f"returns to its own result: {where}")
        if (step % 2 == 0) != both_filled:
            check.change_mismatch.append(f"parity: {where}")
        if isinstance(change, Fill) and step != 1:
            check.change_mismatch.append(f"filling: {where}")
        if grouped.states.depth[state] == grouped.round_of[start] and step > 1:
            check.change_mismatch.append(f"from a state asserting the fewest: {where}")
        even += step % 2 == 0
    return {
        "changes_checked": checked,
        "changes_moving_the_cost_by_an_even_number": even,
        "how_each_kind_moves_the_cost": dict(sorted(moves_seen.items())),
    }


def check_respect(grouped: Grouped, check: FillCheck, most_terms: int = 3) -> dict[str, object]:
    """Filling respects the sameness: on results with at most `most_terms` terms, every filling (and every
    addition of an assertion) performed on each of the result's reached states lands on one result."""
    tried = 0
    for key, members in grouped.members.items():
        if key[0] > most_terms or len(members) < 2:
            continue
        rep = members[0]
        others = [align(m, rep) for m in members[1:]]
        for change in moves(rep):
            if not isinstance(change, Fill) and change.kind is not Kind.ADD_ASSERTION:
                continue
            want = outcome_key(rep, change)
            for m in others:
                tried += 1
                if outcome_key(m, change) != want:
                    check.respect_mismatch.append(f"{_name(grouped, key)} / {written(change, rep)} on {m.key()}")
    return {"outcomes_compared": tried}


def compare_twentythird(grouped: Grouped, check: FillCheck) -> dict[str, object]:
    """The twenty-third's run at the same bounds: its results are the results here with no filled term."""
    comp = compare_with_twentythird(grouped)
    for label, keys in (
        ("missing", comp.missing),
        ("extra", comp.extra),
        ("round differs", comp.round_differs),
        ("shortest sequences differ", comp.sequences_differ),
    ):
        for k in keys:
            check.twentythird_mismatch.append(f"{label}: {key_text(k)}")
    return {
        "twentythird_results": len(comp.twentythird.round_of),
        "results_here_with_no_filled_term": sum(1 for k in grouped.round_of if not any(k[2])),
        "twentythird_results_the_forgetting_map_lands_on": comp.forgotten_onto,
        "most_results_here_forgotten_onto_one": comp.largest_fibre,
    }


def check_read_back(grouped: Grouped, check: FillCheck) -> dict[str, object]:
    """The map back: the original on every result with no filled term; "none" exactly with a filled term; the
    first "none" is the one-term result, filled, at round 2, and the only "none" of that round."""
    none = 0
    for key in grouped.round_of:
        back = read_back(key)
        filled = any(key[2])
        none += back is None
        if filled != (back is None) or (back is not None and back != key23(grouped.representative(key).base)):
            check.read_back_mismatch.append(_name(grouped, key))
    first = smallest_none(grouped)
    nones_at_two = [k for k in grouped.round_of if grouped.round_of[k] == 2 and read_back(k) is None]
    if grouped.rounds >= 2 and (first != (1, (0,), (1,)) or len(nones_at_two) != 1):
        check.read_back_mismatch.append("the first result answered none is not one term, filled, at round 2, alone")
    return {
        "results_answered_none": none,
        "first_result_answered_none": None if first is None else grouped.representative(first).written(),
        "its_round": None if first is None else grouped.round_of[first],
    }


def check_forget(grouped: Grouped, check: FillCheck) -> None:
    """The forgetting map: every result to the twenty-third result of its states (against the twenty-third's
    own mark); every change, forgotten, is a change of the twenty-third seed or, for a filling, none: the
    forgotten outcome is one of the twenty-third's outcomes of the forgotten state, or that state."""
    for key in grouped.round_of:
        if forget_key(key) != key23(grouped.representative(key).base):
            check.forget_mismatch.append(_name(grouped, key))
    outcomes: dict[FState, set[tuple[int, tuple[int, ...]]]] = {}
    for state, change, raw, _ in performed(grouped.states):
        if state not in outcomes:
            outcomes[state] = {key23(perform23(state.base, c)) for c in changes23(state.base)}
        if isinstance(change, Fill):
            ok = key23(raw.base) == key23(state.base)
        else:
            ok = key23(raw.base) in outcomes[state]
        if not ok:
            check.forget_mismatch.append(f"{state.key()} / {written(change, state)}")


def check_reach(grouped: Grouped, check: FillCheck) -> tuple[dict[str, object], list[list[object]]]:
    """The reachability criterion of the exploration's reading against a search along the changes."""
    graph = search_graph(grouped)
    keys = grouped.ordered_keys()
    rows: list[list[object]] = []
    ordered = 0
    reading = grouped.states.reading
    for s in keys:
        found = reached_by_search(grouped, graph, s)
        count = 0
        for t in keys:
            here = reachable(grouped.representative(s), grouped.representative(t), reading)
            if here != (t in found):
                check.reach_mismatch.append(f"{reading.tag}: {key_text(s)} -> {key_text(t)}")
            count += here
        ordered += count
        rows.append([reading.identify, key_text(s), grouped.representative(s).written(), grouped.round_of[s], count])
    return {
        "reading": reading.tag,
        "results": len(keys),
        "ordered_pairs": len(keys) ** 2,
        "ordered_pairs_reachable": ordered,
    }, rows


def check_sameness(small: int, large: int, check: FillCheck) -> dict[str, object]:
    """The equivalence the seed's clauses generate on states with filled terms, by search, against the mark."""
    out: dict[str, object] = {}
    for n in (1, 2):
        roots = generated_classes(n, small, large)
        by_root: dict[FState, Key24] = {}
        by_key: dict[Key24, FState] = {}
        for s, root in roots.items():
            k = result_key(s)
            if by_root.setdefault(root, k) != k:
                check.sameness_mismatch.append(f"joined but not the same: {s.key()}")
            if by_key.setdefault(k, root) != root:
                check.sameness_mismatch.append(f"the same but not joined: {s.key()}")
        out[f"{n}_terms"] = {"states": len(roots), "classes": len(set(roots.values())), "results": len(by_key)}
    return out


def check_readings(bound: int, rounds: int, check: FillCheck, chosen: Grouped) -> dict[str, object]:
    """C-F2 (rounds against the counted cost), C-F3, C-F4, C-I2, C-I3, C-E′ (the chosen results and rounds)."""
    out: dict[str, object] = {"bound_on_terms": bound, "rounds": rounds, "C-F1_C-I1_results": len(chosen.round_of)}
    counted = explore(bound, rounds, Reading(fill=FILL_COUNT))
    for key, r in counted.round_of.items():
        if cost_counted(counted.representative(key)) != r:
            check.readings_mismatch.append(f"C-F2: {key_text(key)}")
    out["C-F2_results"] = len(counted.round_of)
    out["C-F2_results_per_round"] = [sum(1 for r in counted.round_of.values() if r == k) for k in range(rounds + 1)]
    out["C-F1_results_per_round"] = [sum(1 for r in chosen.round_of.values() if r == k) for k in range(rounds + 1)]
    others = {
        "C-F3": explore(bound, rounds, Reading(fill=FILL_LOOPS)),
        "C-F4": explore(bound, rounds, Reading(fill=FILL_BALANCE)),
        "C-I2": explore(bound, rounds, Reading(identify=ID_BOTH)),
        "C-I3": explore(bound, rounds, Reading(identify=ID_NEVER)),
        "C-E′": explore(bound, rounds, plain_states=False),
    }
    for name, grouped in others.items():
        if grouped.round_of != chosen.round_of:
            check.readings_mismatch.append(f"{name}: results or rounds differ from C-F1, C-I1")
        out[f"{name}_results"] = len(grouped.round_of)
        out[f"{name}_states_reached"] = len(grouped.states.depth)
    out["C-F1_C-I1_states_reached"] = len(chosen.states.depth)
    out["identifications_under_C-I2"] = identification_outcomes(chosen, Reading(identify=ID_BOTH))
    out["identifications_under_C-I3"] = identification_outcomes(chosen, Reading(identify=ID_NEVER))
    out["C-N0_results_that_are_the_one_asserting_and_filling_nothing"] = sum(
        1 for k in chosen.round_of if not any(k[1]) and not any(k[2])
    )
    out["C-N0_results_not_that_one_with_every_filled_term_balancing"] = sum(
        1 for k in chosen.round_of if (any(k[1]) or any(k[2])) and class_from_key(k) != "told"
    )
    return out


def check_record_question(grouped: Grouped, check: FillCheck) -> dict[str, object]:
    """The twenty-third's record: the witnesses record the same and are kept by different numbers of terms;
    over the twenty-third's results, it records no assertion exactly for the result asserting nothing."""
    comp = compare_with_twentythird(grouped)
    question = record_question(comp.twentythird)
    rows = []
    for a, b in record_witnesses():
        ra, rb = record23(a), record23(b)
        sa, sb = keeping_size(a), keeping_size(b)
        if ra != rb or sa == sb:
            check.record_question_mismatch.append(f"{a.written()} / {b.written()}")
        rows.append({"first": a.written(), "second": b.written(), "record": list(ra), "kept_by": [sa, sb]})
    if not question.whether_shown:
        check.record_question_mismatch.append("the record's assertions are zero on a result other than nothing")
    return {
        "witnesses": rows,
        "records_among_twentythird_results": question.records,
        "records_holding_results_kept_by_different_numbers_of_terms": question.records_with_several_sizes,
        "records_holding_results_with_different_numbers_of_keeping_terms": question.records_with_several_term_counts,
        "first_such_record": None
        if question.first is None
        else {"record": list(question.first[0]), "results": list(question.first[1])},
    }


def audit(bound: int, rounds: int) -> FillCheck:
    """Every differential check at small bounds, writing nothing: the mutation gate's assay."""
    check = FillCheck()
    grouped = explore(bound, rounds)
    check_results(grouped, check)
    check_sequences(grouped, check)
    check_changes(grouped, check)
    check_respect(grouped, check)
    compare_twentythird(grouped, check)
    check_read_back(grouped, check)
    check_forget(grouped, check)
    for how in (ID_EITHER, ID_BOTH, ID_NEVER):
        check_reach(explore(2, 3, Reading(identify=how)), check)
    check_sameness(1, 3, check)
    check_readings(2, 4, check, explore(2, 4))
    check_record_question(grouped, check)
    return check


# --- writing ----------------------------------------------------------------------------


def write_run(out: Path, bound: int, rounds: int, check: FillCheck) -> dict[str, object]:
    """One exploration: its results, rounds, frontier and statements; every check on it."""
    grouped = explore(bound, rounds)
    tag = run_tag(bound, rounds)
    check_results(grouped, check)
    sequences = check_sequences(grouped, check)
    changes = check_changes(grouped, check)
    respect = check_respect(grouped, check)
    twentythird = compare_twentythird(grouped, check)
    back = check_read_back(grouped, check)
    check_forget(grouped, check)
    counts = shortest_sequences(grouped)
    rows = []
    classes: dict[str, int] = {}
    for key in grouped.ordered_keys():
        rep = grouped.representative(key)
        n, in_r, in_s = record23(rep.base)
        cls = class_from_key(key)
        classes[cls] = classes.get(cls, 0) + 1
        back_key = read_back(key)
        rows.append([
            key_text(key),
            rep.written(),
            n,
            sum(1 for f in key[2] if f),
            grouped.round_of[key],
            in_r,
            in_s,
            " ".join(f"{x}:{'balances' if b else 'does not balance'}" for x, b in key_balance(key)) or "-",
            cls,
            keeping_size(rep.base),
            len(grouped.fewest_members(key)),
            len(grouped.members[key]),
            counts[key],
            "none" if back_key is None else f"{back_key[0]}:" + ",".join(str(e) for e in back_key[1]),
        ])
    _write_csv(
        out / f"results_{tag}.csv",
        ["result", "first_state_reached", "terms", "filled_terms", "round_and_cost", "record_r", "record_s",
         "which_filled_terms_balance", "against_the_one_asserting_nothing", "fewest_terms_keeping_it_from_nothing",
         "states_asserting_the_fewest", "states_reached", "shortest_sequences", "map_back"],
        rows,
    )
    expl = grouped.states
    new_results = [0] * (rounds + 1)
    for r in grouped.round_of.values():
        new_results[r] += 1
    _write_csv(
        out / f"rounds_{tag}.csv",
        ["round", "new_states", "new_results", "attempts_so_far", "results_with_at_most_two_terms_closed_form"],
        [[r, expl.new_per_round[r], new_results[r], expl.attempts_per_round[r], two_term_round_count(r)]
         for r in range(rounds + 1)],
    )
    _write_csv(
        out / f"frontier_{tag}.csv",
        ["state", "written", "change", "result_of_the_state"],
        [[e.state.key(), e.state.written(), written(e.change, e.state), key_text(result_key(e.state))]
         for e in expl.frontier],
    )
    _write_csv(
        out / f"follows_{tag}.csv",
        ["statement", "wording", "in_every_result", "holds_at", "fails_at", "depends_at", "results_where_it_depends"],
        [[v.statement, v.wording, int(v.in_every_result),
          "" if v.holds_at is None else key_text(v.holds_at),
          "" if v.fails_at is None else key_text(v.fails_at),
          "" if v.depends_at is None else key_text(v.depends_at),
          v.results_where_it_depends] for v in verdicts(grouped)],
    )
    return {
        "states_reached": len(expl.depth),
        "results": len(grouped.round_of),
        "results_by_terms": [sum(1 for k in grouped.round_of if k[0] == n) for n in range(bound + 1)],
        "results_by_how_they_stand_against_the_one_asserting_nothing": dict(sorted(classes.items())),
        "new_results_per_round": new_results,
        "frontier_entries": len(expl.frontier),
        "results_of_the_last_round": new_results[rounds],
        "shortest_sequences": sequences,
        "changes": changes,
        "respect": respect,
        "twentythird": twentythird,
        "map_back": back,
    }


def write_counts(out: Path, plan: Plan, check: FillCheck) -> dict[str, object]:
    """The independent counts: by terms, filled terms and assertions; the two-term closed form for every round
    up to `closed_form_upto`, checked against a listing of points; results per round without a bound on
    terms."""
    rows = []
    for bound, rounds in plan.runs():
        for label, c in counts_within(bound, rounds).items():
            rows.append([run_tag(bound, rounds), label, c])
    _write_csv(out / "counts.csv", ["run", "terms/filled/assertions", "results"], rows)
    for k in (0, 1, 2):
        for t in range(plan.points_upto + 1):
            if two_term_count(k, t) != two_term_count_by_points(k, t):
                check.two_term_mismatch.append(f"k={k}, t={t}")
    closed = [two_term_round_count(r) for r in range(plan.closed_form_upto + 1)]
    return {
        "results_of_round_r_with_at_most_two_terms": closed,
        "their_sum_over_rounds_0_to_100": sum(closed),
        "results_of_round_r_without_a_bound_on_terms": layer_counts(plan.layers_upto),
    }


def write_log(out: Path, plan: Plan) -> int:
    """Every attempt at a small bound, one JSON object per line."""
    grouped = explore(plan.log_bound, plan.log_rounds, keep_log=True)
    lines = []
    for a in grouped.states.log:
        lines.append(json.dumps({
            "state": a.state.written(),
            "change": written(a.change, a.state),
            "kind": kind_of(a.change),
            "state_reached": a.raw.written(),
            "beyond_the_bound": a.beyond,
            "kept_as": None if a.outcome is None else a.outcome.written(),
            "result": key_text(result_key(a.raw)),
            "cost_of_the_result": cost(a.raw),
        }, sort_keys=True, ensure_ascii=True))
    (out / f"attempts_{run_tag(plan.log_bound, plan.log_rounds)}.jsonl").write_text(
        "\n".join(lines) + "\n", encoding="utf-8", newline="\n"
    )
    return len(lines)


def write_reach(out: Path, plan: Plan, check: FillCheck) -> dict[str, object]:
    """Reachability under C-I1, C-I2, C-I3 against a search."""
    summaries: dict[str, object] = {}
    rows: list[list[object]] = []
    for how in (ID_EITHER, ID_BOTH, ID_NEVER):
        summary, part = check_reach(explore(plan.reach_bound, plan.reach_rounds, Reading(identify=how)), check)
        summaries[how] = summary
        rows += part
    _write_csv(
        out / f"reach_{run_tag(plan.reach_bound, plan.reach_rounds)}.csv",
        ["identify_reading", "result", "first_state_reached", "round", "results_reachable"],
        rows,
    )
    return summaries


def write_given(out: Path, plan: Plan, check: FillCheck) -> dict[str, object]:
    """The witnesses the paper cites, computed."""
    one_filled = FState(DState(1, (0,), (0,)), (1,))
    pair_filled = FState(DState(2, (0,) * 4, (0,) * 4), (1, 1))
    merged = perform24(pair_filled, Change(Kind.IDENTIFY, "", 0, 1))
    arb_filled = FState(DState.of(2, [(0, 1)]), (1, 1))
    arb_merged = perform24(arb_filled, Change(Kind.IDENTIFY, "", 0, 1))
    given = {
        "the_twentythird_record_question": check_record_question(explore(3, 6), check),
        "identifying_two_filled_terms": {
            "from": pair_filled.written(), "cost_from": cost(pair_filled),
            "to": merged.written(), "cost_to": cost(merged),
        },
        "identifying_turns_a_two_term_witness_into_a_loop": {
            "from": arb_filled.written(), "class_from": tell_class(arb_filled),
            "to": arb_merged.written(), "class_to": tell_class(arb_merged),
        },
        "smallest_result_answered_none": {"state": one_filled.written(), "cost": cost(one_filled)},
        "first_result_of_each_class": _first_of_each_class(explore(3, 5)),
    }
    _write_json(out / "given.json", given)
    return {"witnesses": sorted(given)}


def _first_of_each_class(grouped: Grouped) -> dict[str, str]:
    out: dict[str, str] = {}
    for key in grouped.ordered_keys():
        out.setdefault(class_from_key(key), grouped.representative(key).written())
    return dict(sorted(out.items()))


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    check = FillCheck()
    summary: dict[str, object] = {
        "plan": {
            "runs": [list(run) for run in plan.runs()],
            "full_log": [plan.log_bound, plan.log_rounds],
            "reachability": [plan.reach_bound, plan.reach_rounds],
            "generated_sameness_checked_on": [plan.same_small, plan.same_large],
            "readings": [plan.readings_bound, plan.readings_rounds],
        },
        "given": write_given(out, plan, check),
        "independent_counts": write_counts(out, plan, check),
    }
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, check)
    summary["runs"] = runs
    summary["reachability"] = write_reach(out, plan, check)
    summary["attempts_in_full_log"] = write_log(out, plan)
    summary["generated_sameness"] = check_sameness(plan.same_small, plan.same_large, check)
    readings = check_readings(
        plan.readings_bound, plan.readings_rounds, check, explore(plan.readings_bound, plan.readings_rounds)
    )
    _write_json(out / "readings.json", readings)
    summary["disagreements"] = check.as_dict()
    summary["every_check_clean"] = check.clean()
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
