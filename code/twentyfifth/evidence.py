"""Writes `evidence/twentyfifth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/run_twentyfifth.py` from the repository root.  No file holds a
date, a duration, or a machine name.

Every differential check of this derivation records its disagreements in one
dataclass, `FillingCheck`; every list must be empty on correct code, and each
has an injection test (`tests/test_twentyfifth_evidence.py`) and a mutation in
the twenty-fifth panel of `ci/check_mutation_bite.py`.

Cited from the first derivation (`xry.evidence`) and re-checked (no change)
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on which changes there are or on when two states are one result.

Cited from the twenty-third derivation and re-checked (computed again)
    Its exploration (`twentythird.explore`) is run at the same bounds: its
    results must be exactly the results here with nothing filled, at the same
    rounds (`embed_mismatch`).  Its closed form for the results with at most two
    terms must still hold (`two_term_mismatch`): nothing can be filled there.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field, fields
from itertools import combinations, permutations, product
from pathlib import Path

from ninth.changes import Change, Kind
from twentythird.explore import explore as explore23
from twentythird.state import is_nothing, nothing_certificate, plain_cost, plain_of, written
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from twentyfifth.cost import cost, cost23, record
from twentyfifth.embed import compare_twentythird, forget_fibres, read_back, read_back_of_mark, seventh_pairs_merged
from twentyfifth.embed import smallest_none
from twentyfifth.explore import Grouped, explore, order, performed, shortest_sequences
from twentyfifth.follows import verdicts
from twentyfifth.orbits import counts_within, two_term_round_count
from twentyfifth.reach import reachable, reached_by_search, search_graph
from twentyfifth.readings import CHOSEN, READINGS, ReadingRun, explore_reading, i3_reach_failures
from twentyfifth.state import (
    Change25,
    DState,
    FState,
    Filling,
    Mark,
    Triple,
    align,
    balances,
    embed,
    oriented_triples,
    perform,
    rename_triples,
    result_mark,
    swap25,
    written25,
)
from twentyfifth.told import (
    blind,
    blind_by_description,
    decides,
    keeping_sets,
    keeping_sets_by_restriction,
    rank,
    record_differs_from_nothing,
    told,
    undecided_witness,
    why_not_told,
)

__all__ = [
    "FillingCheck",
    "Plan",
    "audit",
    "check_changes",
    "check_counts",
    "check_decide",
    "check_embed",
    "check_read_back",
    "check_reach",
    "check_readings",
    "check_results",
    "check_whether",
    "compare_evidence",
    "run_tag",
    "unseen_rows",
    "write_all",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Three explorations (`runs`: terms and rounds); a full attempt log at
    (`log_bound`, `log_rounds`); reachability among the results of
    (`reach_bound`, `reach_rounds`); the unchosen readings at
    (`readings_bound`, `readings_rounds`); the sets of triples that decide, up to
    rewriting, with at most `decide_terms` terms, searched over small excess
    tables with at most `search_terms`; the sets of terms keeping a result from
    nothing found by reading every set of terms with at most `keeping_terms`.
    """

    bound: int = 5
    rounds: int = 8
    deep_bound: int = 3
    deep_rounds: int = 10
    two_term_rounds: int = 24
    log_bound: int = 3
    log_rounds: int = 5
    reach_bound: int = 3
    reach_rounds: int = 5
    readings_bound: int = 3
    readings_rounds: int = 6
    decide_terms: int = 5
    search_terms: int = 4
    unseen_terms: int = 4
    unseen_full_upto: int = 6
    keeping_terms: int = 5
    count_runs: tuple[tuple[int, int], ...] = ((3, 9), (4, 8), (5, 8))

    def runs(self) -> tuple[tuple[int, int], ...]:
        """(terms, rounds) of the explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


@dataclass
class FillingCheck:
    """Every disagreement found by the differential checks; all lists empty on correct code."""

    round_not_cost: list[str] = field(default_factory=list)
    plain_mismatch: list[str] = field(default_factory=list)
    count_mismatch: list[str] = field(default_factory=list)
    two_term_mismatch: list[str] = field(default_factory=list)
    record_mismatch: list[str] = field(default_factory=list)
    told_mismatch: list[str] = field(default_factory=list)
    blind_mismatch: list[str] = field(default_factory=list)
    keeping_mismatch: list[str] = field(default_factory=list)
    whether_mismatch: list[str] = field(default_factory=list)
    decide_mismatch: list[str] = field(default_factory=list)
    change_mismatch: list[str] = field(default_factory=list)
    embed_mismatch: list[str] = field(default_factory=list)
    read_back_mismatch: list[str] = field(default_factory=list)
    reach_mismatch: list[str] = field(default_factory=list)
    exchange_mismatch: list[str] = field(default_factory=list)
    readings_mismatch: list[str] = field(default_factory=list)

    def clean(self) -> bool:
        """No disagreement anywhere."""
        return not any(getattr(self, f.name) for f in fields(self))

    def as_dict(self) -> dict[str, list[str]]:
        """Every list, by name."""
        return {f.name: list(getattr(self, f.name)) for f in fields(self)}


def mark_text(mark: Mark) -> str:
    """A result's mark, written: its terms, its normal excess table, its filled triples."""
    n, table, filled = mark
    return f"{n}:" + ",".join(str(e) for e in table) + "|" + ".".join(f"{x}{y}{z}" for x, y, z in filled)


def _name(grouped: Grouped, mark: Mark) -> str:
    return f"{mark_text(mark)} ({written25(grouped.representative(mark))})"


def psi(fs: FState) -> int:
    """The twenty-second's cost of the assertions (`phi`) plus the filled triples."""
    return plain_cost(fs.state) + len(fs.filled)


def nothing_mark(fs: FState) -> Mark:
    """The mark of the result asserting nothing on `fs`'s terms with its filled triples."""
    n = fs.n
    return result_mark(FState(DState(n, (0,) * (n * n), (0,) * (n * n)), fs.filled))


# --- checks on one exploration ---------------------------------------------------------


def check_results(grouped: Grouped, check: FillingCheck, keeping_terms: int) -> dict[str, object]:
    """Every result: its round against its cost; its balance record on every state of it; told against the two
    records compared; blind against its description and against filling every triple; its least keeping sets by
    sums and by reading every set of terms; the exchange.  Returns counts of why results are not told."""
    why: dict[str, int] = {}
    for mark in grouped.round_of:
        rep = grouped.representative(mark)
        r = grouped.round_of[mark]
        name = _name(grouped, mark)
        if cost(rep) != r:
            check.round_not_cost.append(name)
        for m in grouped.members[mark][1:]:
            moved = align(m, rep)
            if [balances(moved, t) for t in rep.filled] != [balances(rep, t) for t in rep.filled]:
                check.record_mismatch.append(f"{name} / {m.key()}")
        is_told = told(rep)
        if is_told != record_differs_from_nothing(rep) or (is_told and mark == nothing_mark(rep)):
            check.told_mismatch.append(name)
        full = FState(rep.state, oriented_triples(rep.n))
        if blind(rep.state) != blind_by_description(rep.state) or blind(rep.state) == told(full):
            check.blind_mismatch.append(name)
        sets = keeping_sets(rep.state)
        if rep.n <= keeping_terms and sets != keeping_sets_by_restriction(rep.state):
            check.keeping_mismatch.append(f"least sets: {name}")
        if (not sets) != (nothing_certificate(rep.state) is None):
            check.keeping_mismatch.append(f"none exactly for nothing: {name}")
        for t in rep.filled:
            if not balances(rep, t) and not any(set(s) <= set(t) for s in sets):
                check.keeping_mismatch.append(f"an unbalanced filled triple keeps nothing: {name}")
        image = result_mark(swap25(rep))
        if image not in grouped.round_of or grouped.round_of[image] != r or told(swap25(rep)) != is_told:
            check.exchange_mismatch.append(name)
        reason = why_not_told(rep)
        why[reason] = why.get(reason, 0) + 1
    return {"results_by_why_they_are_told_or_not": dict(sorted(why.items()))}


def check_counts(grouped: Grouped, check: FillingCheck) -> None:
    """The explored results by terms, assertions and filled triples against the independent count; the results with
    at most two terms against the twenty-third's closed form."""
    explored: dict[str, int] = {}
    for mark, r in grouped.round_of.items():
        n, _, filled = mark
        label = f"{n}/{r - n - len(filled)}/{len(filled)}"
        explored[label] = explored.get(label, 0) + 1
    independent = counts_within(grouped.bound, grouped.rounds)
    for label in sorted(set(explored) | set(independent)):
        if explored.get(label, 0) != independent.get(label, 0):
            check.count_mismatch.append(f"{label}: explored {explored.get(label, 0)}, counted {independent.get(label, 0)}")
    per_round = [0] * (grouped.rounds + 1)
    for mark, r in grouped.round_of.items():
        per_round[r] += mark[0] <= 2
    for r, got in enumerate(per_round):
        if got != two_term_round_count(r):
            check.two_term_mismatch.append(f"round {r}: explored {got}, closed form {two_term_round_count(r)}")


def _kind(change: Change25) -> str:
    return "fill three different terms" if isinstance(change, Filling) else change.kind.value


def check_changes(grouped: Grouped, check: FillingCheck) -> dict[str, object]:
    """Every change of every explored state: the round of a state is `phi` plus its filled triples; a filling raises
    the cost of the result by exactly one; a change from a state asserting the fewest raises it by at most one; no
    change returns a state to its own result.  Returns how each kind moves the cost."""
    for fs, r in grouped.states.depth.items():
        if psi(fs) != r:
            check.plain_mismatch.append(fs.key())
    moves: dict[str, int] = {}
    for fs, change, _, out in performed(grouped.states):
        start = result_mark(fs)
        end = result_mark(out)
        step = grouped.round_of[end] - grouped.round_of[start]
        if end == start or (isinstance(change, Filling) and step != 1):
            check.change_mismatch.append(f"{fs.key()} / {_kind(change)}")
        if grouped.states.depth[fs] == grouped.round_of[start] and step > 1:
            check.change_mismatch.append(f"from a state asserting the fewest: {fs.key()} / {_kind(change)}")
        label = f"{_kind(change)} {step:+d}"
        moves[label] = moves.get(label, 0) + 1
    return {"how_each_kind_moves_the_cost": dict(sorted(moves.items()))}


def check_embed(grouped: Grouped, check: FillingCheck) -> dict[str, object]:
    """The twenty-third's exploration at the same bound, mapped in with nothing filled, against the results here
    with nothing filled; the seventh's and the first's pairs stay merged; forgetting the filled triples."""
    report = compare_twentythird(grouped, explore23(grouped.bound, grouped.rounds))
    if report.missing_here or report.extra_here or report.rounds_differing:
        check.embed_mismatch.append(f"{report}")
    if report.returned_the_original != report.twentythird_results:
        check.embed_mismatch.append("the map back does not return a mapped result")
    if seventh_pairs_merged() != (True, True):
        check.embed_mismatch.append("an earlier pair kept apart")
    fibres = forget_fibres(grouped)
    return {
        "twentythird_results": report.twentythird_results,
        "results_here_with_nothing_filled": report.results_with_nothing_filled,
        "map_back_returns_the_original_on_every_mapped_result": report.returned_the_original
        == report.twentythird_results,
        "twentythird_results_reached_by_forgetting": len(fibres),
        "most_results_here_forgotten_onto_one": max(fibres.values()),
    }


def check_read_back(grouped: Grouped, check: FillingCheck) -> dict[str, object]:
    """The map back from a result's state against the map back from its mark; the first result answered "none"."""
    none = 0
    for mark in grouped.round_of:
        back = read_back(grouped.representative(mark))
        none += back is None
        if back != read_back_of_mark(mark):
            check.read_back_mismatch.append(_name(grouped, mark))
    first = smallest_none(grouped)
    if grouped.bound >= 3 and grouped.rounds >= 4 and first != (3, (0,) * 9, ((0, 1, 2),)):
        check.read_back_mismatch.append(f"the first result answered none is {first}")
    return {
        "results_answered_none": none,
        "first_result_answered_none": None if first is None else written25(grouped.representative(first)),
        "its_round": None if first is None else grouped.round_of[first],
    }


def check_reach(grouped: Grouped, check: FillingCheck) -> tuple[dict[str, object], list[list[object]]]:
    """The reachability criterion against a search along the changes, on every ordered pair of results."""
    graph = search_graph(grouped)
    marks = grouped.ordered_marks()
    rows: list[list[object]] = []
    ordered = 0
    for s in marks:
        found = reached_by_search(grouped, graph, s)
        count = 0
        for t in marks:
            here = reachable(grouped.representative(s), grouped.representative(t))
            if here != (t in found):
                check.reach_mismatch.append(f"{mark_text(s)} -> {mark_text(t)}")
            count += here
        ordered += count
        rows.append([mark_text(s), written25(grouped.representative(s)), grouped.round_of[s], count, len(found)])
    return {
        "bound_on_terms": grouped.bound,
        "rounds": grouped.rounds,
        "results": len(marks),
        "ordered_pairs": len(marks) ** 2,
        "ordered_pairs_reachable": ordered,
    }, rows


def _sorted3(a: int, b: int, c: int) -> Triple:
    x, y, z = sorted((a, b, c))
    return (x, y, z)


def _triple_sets(n: int) -> list[tuple[Triple, ...]]:
    """Every set of three-term sets of `n` terms, up to rewriting (least writing first)."""
    triples = list(combinations(range(n), 3))
    seen: set[tuple[Triple, ...]] = set()
    out: list[tuple[Triple, ...]] = []
    for k in range(len(triples) + 1):
        for sub in combinations(triples, k):
            best = min(
                tuple(sorted(_sorted3(p[x], p[y], p[z]) for x, y, z in sub)) for p in permutations(range(n))
            )
            if best not in seen:
                seen.add(best)
                out.append(best)
    return out


def _balanced_small(n: int, triples: tuple[Triple, ...]) -> bool:
    """Is some excess table with every loop and two-way sum zero, entries −1, 0, 1, balancing every triple given,
    not the result asserting nothing?"""
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
    for values in product((-1, 0, 1), repeat=len(pairs)):
        table = [0] * (n * n)
        for (x, y), v in zip(pairs, values):
            table[x * n + y] = v
            table[y * n + x] = -v
        state = plain_of(n, tuple(table))
        if all(balances(FState(state, ()), t) for t in triples) and not is_nothing(state):
            return True
    return False


def check_decide(plan: Plan, check: FillingCheck) -> tuple[dict[str, object], list[list[object]]]:
    """The sets of three terms, up to rewriting, with at most `decide_terms` terms: the rank condition against a
    witness (verified) and, up to `search_terms` terms, against a search over small excess tables."""
    rows: list[list[object]] = []
    summary: dict[str, object] = {}
    for n in range(3, plan.decide_terms + 1):
        classes = _triple_sets(n)
        by_size: dict[int, list[int]] = {}
        for sub in classes:
            d = decides(n, sub)
            witness = undecided_witness(n, sub)
            if witness is not None:
                state = plain_of(n, witness)
                good = all(balances(FState(state, ()), t) for t in sub) and not is_nothing(state)
            else:
                good = False
            if d == (witness is not None) or (witness is not None and not good):
                check.decide_mismatch.append(f"{n} terms: {sub}")
            if n <= plan.search_terms and d == _balanced_small(n, sub):
                check.decide_mismatch.append(f"search, {n} terms: {sub}")
            by_size.setdefault(len(sub), [0, 0])[0 if d else 1] += 1
            rows.append([n, len(sub), " ".join(f"{x}{y}{z}" for x, y, z in sub), int(d), "" if witness is None else
                         written(plain_of(n, witness))])
        labelled: dict[int, list[int]] = {}
        for k in range(len(list(combinations(range(n), 3))) + 1):
            for sub in combinations(combinations(range(n), 3), k):
                labelled.setdefault(k, [0, 0])[0 if decides(n, sub) else 1] += 1
        summary[f"{n}_terms"] = {
            "sets_up_to_rewriting": len(classes),
            "deciding_and_not_by_size": {str(k): v for k, v in sorted(by_size.items())},
            "fewest_triples_that_decide": min(k for k, (d, _) in by_size.items() if d),
            "labelled_sets_deciding_and_not_by_size": {str(k): v for k, v in sorted(labelled.items())},
        }
    return summary, rows


def unseen_rows(plan: Plan) -> list[list[object]]:
    """For every set of filled triples (each way round) up to rewriting with at most `unseen_terms` terms: how many
    independent directions of the results it never tells (the excess tables modulo raising, less the rank of its
    sums around)."""
    rows: list[list[object]] = []
    for n in range(3, plan.unseen_terms + 1):
        triples = oriented_triples(n)
        seen: set[tuple[Triple, ...]] = set()
        for k in range(len(triples) + 1):
            for sub in combinations(triples, k):
                best = min(rename_triples(sub, p) for p in permutations(range(n)))
                if best in seen:
                    continue
                seen.add(best)
                matrix = []
                for x, y, z in best:
                    row = [0] * (n * n)
                    for a, b in ((x, y), (y, z), (z, x)):
                        row[a * n + b] += 1
                    matrix.append(row)
                r = rank(matrix) if matrix else 0
                rows.append([n, k, " ".join(f"{x}{y}{z}" for x, y, z in best), n * n - (n - 1) - r, n])
    for n in range(plan.unseen_terms + 1, plan.unseen_full_upto + 1):
        triples = oriented_triples(n)
        matrix = []
        for x, y, z in triples:
            row = [0] * (n * n)
            for a, b in ((x, y), (y, z), (z, x)):
                row[a * n + b] += 1
            matrix.append(row)
        rows.append([n, 0, "", n * n - (n - 1), n])
        rows.append([n, len(triples), "every triple", n * n - (n - 1) - rank(matrix), n])
    return rows


def check_readings(plan: Plan, check: FillingCheck) -> dict[str, object]:
    """Every reading at the small bound: its rounds against its cost formula; C-I2 and fillings last against the
    chosen reading; the chosen reading against the main exploration; C-F2 against the twenty-third; C-I3's cost and
    reachability failures."""
    bound, rounds = plan.readings_bound, plan.readings_rounds
    main = explore(bound, rounds)
    runs: dict[str, ReadingRun] = {r.name: explore_reading(r, bound, rounds) for r in READINGS}
    chosen = runs[CHOSEN.name]
    if chosen.round_of != main.round_of:
        check.readings_mismatch.append("the chosen reading, computed twice")
    out: dict[str, object] = {"bound_on_terms": bound, "rounds": rounds}
    witness: dict[str, object] = {}
    for name, run in runs.items():
        wrong = sorted((m for m in run.round_of if run.cost(m) != run.round_of[m]), key=lambda m: run.round_of[m])
        if run.reading.identify == "keep":
            reaching, filled = i3_reach_failures(run)
            if reaching or not wrong:
                check.readings_mismatch.append(name)
            witness = {"results_with_a_filled_triple": filled, "of_which_reach_a_result_with_none": reaching}
            for m in wrong[:1]:
                first_state, first_filled = run.first[m]
                witness["state"] = written(first_state)
                witness["filled_triples"] = [list(t) for t in first_filled]
                witness["round"] = run.round_of[m]
                witness["cost_by_the_formula"] = run.cost(m)
        elif wrong:
            check.readings_mismatch.append(f"{name}: round against cost")
        if run.reading.identify == "drop" or run.reading.fills_last:
            if run.round_of != chosen.round_of:
                check.readings_mismatch.append(f"{name}: not the chosen results")
        if not run.reading.fill_changes_state:
            theirs = explore23(bound, rounds).round_of
            if {(m[0], m[1]): r for m, r in run.round_of.items()} != theirs:
                check.readings_mismatch.append(f"{name}: not the twenty-third's results")
        out[name] = {
            "results": len(run.round_of),
            "results_per_round": run.per_round(),
            "results_told": sum(1 for m in run.round_of if run.told(m)),
            "rounds_against_the_cost_formula": len(run.round_of) - len(wrong),
        }
    out["C-I3_witness"] = witness
    return out


def audit(bound: int = 3, rounds: int = 6, small: Plan | None = None) -> FillingCheck:
    """Every differential check at small bounds, writing nothing: the mutation gate's assay."""
    plan = small if small is not None else Plan(
        readings_bound=3, readings_rounds=5, decide_terms=4, search_terms=4, reach_bound=3, reach_rounds=4
    )
    check = FillingCheck()
    grouped = explore(bound, rounds)
    check_results(grouped, check, plan.keeping_terms)
    check_counts(grouped, check)
    check_changes(grouped, check)
    check_embed(grouped, check)
    check_read_back(grouped, check)
    check_whether(grouped, check)
    check_reach(explore(plan.reach_bound, plan.reach_rounds), check)
    check_decide(plan, check)
    check_readings(plan, check)
    return check


def check_whether(grouped: Grouped, check: FillingCheck) -> tuple[dict[str, object], list[list[object]]]:
    """The twenty-third's question, on the results with nothing filled: the record shows whether a result is the one
    asserting nothing (no assertion recorded exactly then); which records are shared by results kept by sets of
    terms of different sizes."""
    shapes: dict[tuple[int, int, int], dict[tuple[int, ...], str]] = {}
    for mark in grouped.ordered_marks():
        if mark[2]:
            continue
        rep = grouped.representative(mark)
        n, in_r, in_s = record(rep)
        if (in_r + in_s == 0) != (nothing_certificate(rep.state) is None):
            check.whether_mismatch.append(_name(grouped, mark))
        shape = tuple(sorted({len(s) for s in keeping_sets(rep.state)}))
        shapes.setdefault((n, in_r, in_s), {}).setdefault(shape, written(rep.state))
    rows = [
        [n, a, b, len(v), " / ".join(f"{list(k)}: {w}" for k, w in sorted(v.items()))]
        for (n, a, b), v in sorted(shapes.items())
    ]
    shared = [k for k, v in shapes.items() if len(v) > 1]
    first = min(shared, key=lambda k: (k[0] + k[1] + k[2], k)) if shared else None
    return {
        "records": len(shapes),
        "records_shared_by_results_kept_by_sets_of_different_sizes": len(shared),
        "first_such_record": None if first is None else list(first),
        "its_results_by_the_sizes_of_their_least_keeping_sets": None
        if first is None
        else {str(list(k)): w for k, w in sorted(shapes[first].items())},
    }, rows


# --- witnesses --------------------------------------------------------------------------


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the empty beginning, and the witnesses the paper cites."""
    three = DState(3, (0,) * 9, (0,) * 9)
    loop_filled = FState(DState.of(3, [(0, 0)], []), ((0, 1, 2), (0, 2, 1)))
    arb = DState.of(3, [(0, 1)], [])
    blind3 = DState.of(3, [(0, 1), (0, 2)], [(2, 1), (2, 0)])
    blind4 = DState.of(4, [(1, 0), (2, 3)], [(0, 2), (3, 1)])
    two_triples = DState.of(4, [(2, 3)], [(3, 2)])
    arc = DState.of(3, [(0, 1)], [(1, 0)])
    one = FState(three, ((0, 1, 2),))
    merged = perform(one, _identify(0, 1))
    wloop = DState.of(3, [(0, 0)], [(1, 1)])
    wpair = DState.of(3, [(0, 1)], [(1, 2)])
    five_loop = DState.of(5, [(0, 0)], [])
    doc: dict[str, object] = {
        "state": written25(FState(DState(0, (), ()), ())),
        "the_twentythird_record_does_not_show_which_terms": [
            {"state": written(s), "record": list(record(FState(s, ()))), "least_sets_keeping_it_from_nothing":
             [list(k) for k in keeping_sets(s)]}
            for s in (DState.of(2, [(0, 0)], []), DState.of(2, [(0, 1)], []), wloop, wpair, arc)
        ],
        "a_loop_is_never_gone_along": {
            "state": written25(loop_filled),
            "told": told(loop_filled),
            "the_result_asserting_nothing": is_nothing(loop_filled.state),
        },
        "a_two_way_sum_seen_one_way_round": {
            "state": written(arb),
            "balances_a_b_c": balances(FState(arb, ()), (0, 1, 2)),
            "balances_a_c_b": balances(FState(arb, ()), (0, 2, 1)),
        },
        "blind_with_three_terms": {"state": written(blind3), "blind": blind(blind3), "nothing": is_nothing(blind3)},
        "blind_with_four_terms": {"state": written(blind4), "blind": blind(blind4), "nothing": is_nothing(blind4)},
        "blind_with_five_terms_at_a_loop": {"state": written(five_loop), "blind": blind(five_loop)},
        "two_triples_through_a_do_not_decide": {
            "state": written(two_triples),
            "balances_a_b_c": balances(FState(two_triples, ()), (0, 1, 2)),
            "balances_a_b_d": balances(FState(two_triples, ()), (0, 1, 3)),
            "balances_a_c_d": balances(FState(two_triples, ()), (0, 2, 3)),
            "nothing": is_nothing(two_triples),
        },
        "a_b_c_arb_bsa_filled_either_way_round": {
            "state": written(arc),
            "told_filled_a_b_c": told(FState(arc, ((0, 1, 2),))),
            "told_filled_a_c_b": told(FState(arc, ((0, 2, 1),))),
        },
        "identifying_two_terms_of_a_filled_triple": {
            "state": written25(one),
            "cost": cost(one),
            "after_identifying_a_and_b": written25(merged),
            "cost_after": cost(merged),
        },
        "the_map_back": {
            "on_a_b_arb": None if (k := read_back(FState(DState.of(2, [(0, 1)], []), ()))) is None else list(k[1]),
            "on_a_b_c_filled_a_b_c": read_back(one),
        },
        "the_seventh_and_first_pairs_stay_merged": list(seventh_pairs_merged()),
        "the_twentythird_cost_of_a_b_c_arb_bsa_and_with_a_b_c_filled": [cost23(arc), cost(FState(arc, ((0, 1, 2),)))],
    }
    _write_json(out / "given.json", doc)
    return {"witnesses": len(doc)}


def _identify(x: int, y: int) -> Change25:
    return Change(Kind.IDENTIFY, "", x, y)


# --- the files --------------------------------------------------------------------------


RESULT_HEADER = (
    "result",
    "written",
    "terms",
    "recorded_assertions_in_r",
    "recorded_assertions_in_s",
    "filled_triples",
    "balancing",
    "not_balancing",
    "round_first_reached",
    "fewest_changes_by_formula",
    "told",
    "why_told_or_not",
    "blind",
    "least_sets_keeping_it_from_nothing",
    "map_back",
    "exchange",
    "shortest_sequences_of_changes",
)


def write_run(out: Path, bound: int, rounds: int, plan: Plan, check: FillingCheck) -> dict[str, object]:
    """All files of one exploration; returns its summary and fills `check`."""
    tag = run_tag(bound, rounds)
    grouped = explore(bound, rounds)
    results_block = check_results(grouped, check, plan.keeping_terms)
    check_counts(grouped, check)
    changes_block = check_changes(grouped, check)
    embed_block = check_embed(grouped, check)
    back_block = check_read_back(grouped, check)
    whether_block, whether_rows = check_whether(grouped, check)
    sequences = shortest_sequences(grouped)
    rows: list[list[object]] = []
    for mark in grouped.ordered_marks():
        rep = grouped.representative(mark)
        n, in_r, in_s = record(rep)
        back = read_back(rep)
        rows.append(
            [
                mark_text(mark),
                written25(rep),
                n,
                in_r,
                in_s,
                len(rep.filled),
                " ".join(f"{x}{y}{z}" for x, y, z in rep.filled if balances(rep, (x, y, z))),
                " ".join(f"{x}{y}{z}" for x, y, z in rep.filled if not balances(rep, (x, y, z))),
                grouped.round_of[mark],
                cost(rep),
                int(told(rep)),
                why_not_told(rep),
                int(blind(rep.state)),
                " ".join("".join(str(t) for t in s) for s in keeping_sets(rep.state)),
                "none" if back is None else f"{back[0]}:" + ",".join(str(e) for e in back[1]),
                mark_text(result_mark(swap25(rep))),
                sequences[mark],
            ]
        )
    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, rows)
    groups: dict[tuple[int, int, int], int] = {}
    for mark, r in grouped.round_of.items():
        n, _, filled = mark
        key = (n, r - n - len(filled), len(filled))
        groups[key] = groups.get(key, 0) + 1
    _write_csv(
        out / f"added_{tag}.csv",
        ("terms_added_to_given", "assertions_added_to_given", "filled_triples", "results"),
        [[a, b, c, v] for (a, b, c), v in sorted(groups.items(), key=lambda kv: (sum(kv[0]), kv[0]))],
    )
    exits: dict[FState, int] = {}
    for fs, _ in grouped.states.frontier:
        exits[fs] = exits.get(fs, 0) + 1
    _write_csv(
        out / f"frontier_{tag}.csv",
        ("state", "written", "its_result", "round_first_reached", "leaves_by_the_change"),
        [[s.key(), written25(s), mark_text(result_mark(s)), grouped.states.depth[s], exits[s]] for s in
         sorted(exits, key=order)],
    )
    round_rows = []
    so_far = 0
    for r in range(rounds + 1):
        new = [m for m, v in grouped.round_of.items() if v == r]
        so_far += len(new)
        round_rows.append(
            [
                r,
                len(new),
                so_far,
                grouped.states.new_per_round[r],
                sum(1 for m in new if m[0] <= 2),
                two_term_round_count(r),
                sum(1 for m in new if m[2]),
                sum(1 for m in new if told(grouped.representative(m))),
            ]
        )
    _write_csv(
        out / f"rounds_{tag}.csv",
        (
            "round",
            "new_results_within_bound",
            "results_so_far_within_bound",
            "new_states_reached",
            "new_results_with_at_most_two_terms",
            "new_results_with_at_most_two_terms_by_closed_form",
            "new_results_with_a_filled_triple",
            "new_results_told",
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
                "" if v.holds_at is None else written25(grouped.representative(v.holds_at)),
                "" if v.fails_at is None else written25(grouped.representative(v.fails_at)),
                "" if v.depends_at is None else written25(grouped.representative(v.depends_at)),
                v.results_where_it_depends,
            ]
            for v in found
        ],
    )
    _write_csv(
        out / f"records_{tag}.csv",
        ("terms", "recorded_in_r", "recorded_in_s", "sizes_of_least_keeping_sets_seen", "a_result_for_each"),
        whether_rows,
    )
    by_terms: dict[int, int] = {}
    for mark in grouped.round_of:
        by_terms[mark[0]] = by_terms.get(mark[0], 0) + 1
    return {
        "bound_on_terms": bound,
        "rounds": rounds,
        "states_reached": len(grouped.states.depth),
        "results": len(grouped.round_of),
        "results_by_terms": {str(n): by_terms[n] for n in sorted(by_terms)},
        "results_with_a_filled_triple": sum(1 for m in grouped.round_of if m[2]),
        "results_told": sum(1 for m in grouped.round_of if told(grouped.representative(m))),
        "results_blind_not_asserting_nothing": sum(
            1 for m in grouped.round_of if blind(grouped.representative(m).state)
            and not is_nothing(grouped.representative(m).state)
        ),
        "last_round_with_a_new_result": max(grouped.round_of.values()),
        "frontier_states": len(exits),
        "frontier_entries": len(grouped.states.frontier),
        "shortest_sequences_total": sum(sequences.values()),
        "statements_tested": len(found),
        "statements_holding_in_every_result": [v.statement for v in found if v.in_every_result],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
        "statements_depending_on_the_state": [v.statement for v in found if v.depends_at is not None],
        "told_or_not": results_block,
        "changes": changes_block,
        "twentythird_derivation": embed_block,
        "map_back": back_block,
        "the_twentythird_record": whether_block,
    }


def write_reach(out: Path, plan: Plan, check: FillingCheck) -> dict[str, object]:
    """`reach_{tag}.csv`: what each result reaches, by the criterion and by search."""
    grouped = explore(plan.reach_bound, plan.reach_rounds)
    block, rows = check_reach(grouped, check)
    _write_csv(
        out / f"reach_{run_tag(plan.reach_bound, plan.reach_rounds)}.csv",
        ("result", "written", "round", "results_it_reaches", "results_it_reaches_by_search"),
        rows,
    )
    return block


def write_log(out: Path, plan: Plan) -> int:
    """The full attempt log of a small exploration: each outcome state and its result."""
    grouped = explore(plan.log_bound, plan.log_rounds, keep_log=True)
    path = out / f"attempts_{run_tag(plan.log_bound, plan.log_rounds)}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in grouped.states.log:
            line = {
                "state": rec.state.key(),
                "written": written25(rec.state),
                "round": grouped.states.depth[rec.state] + 1,
                "change": rec.change.written(rec.state.state),
                "kind": _kind(rec.change),
                "reaches_the_state": rec.raw.key(),
                "its_result": None if rec.outcome is None else mark_text(result_mark(rec.outcome)),
                "beyond_bound": rec.beyond,
            }
            handle.write(json.dumps(line, sort_keys=True, ensure_ascii=True) + "\n")
    return len(grouped.states.log)


def write_counts(out: Path, plan: Plan) -> dict[str, object]:
    """`counts.csv`: results by terms, assertions and filled triples, by the independent count."""
    rows: list[list[object]] = []
    for n, rounds in plan.count_runs:
        counts = counts_within(n, rounds)
        for label in sorted(counts, key=lambda s: tuple(int(v) for v in s.split("/"))):
            a, b, c = (int(v) for v in label.split("/"))
            if a == n:
                rows.append([a, b, c, a + b + c, counts[label]])
    _write_csv(out / "counts.csv", ("terms", "fewest_assertions", "filled_triples", "cost", "results"), rows)
    return {"rows": len(rows)}


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    check = FillingCheck()
    summary: dict[str, object] = {
        "plan": {
            "runs": [list(run) for run in plan.runs()],
            "full_log": [plan.log_bound, plan.log_rounds],
            "reachability": [plan.reach_bound, plan.reach_rounds],
            "readings": [plan.readings_bound, plan.readings_rounds],
            "sets_of_triples_that_decide_up_to_terms": plan.decide_terms,
            "searched_over_small_excess_tables_up_to_terms": plan.search_terms,
            "least_keeping_sets_by_reading_every_set_of_terms_up_to_terms": plan.keeping_terms,
            "independent_counts_written_at": [list(run) for run in plan.count_runs],
            "directions_never_told_for_every_set_up_to_terms_and_every_triple_up_to_terms": [
                plan.unseen_terms,
                plan.unseen_full_upto,
            ],
        },
        "given": write_given(out),
        "independent_counts": write_counts(out, plan),
    }
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan, check)
    summary["runs"] = runs
    summary["reachability"] = write_reach(out, plan, check)
    summary["attempts_in_full_log"] = write_log(out, plan)
    decide_block, decide_rows = check_decide(plan, check)
    _write_csv(out / "decide.csv", ("terms", "triples", "triples_up_to_rewriting", "decides", "witness_if_not"),
               decide_rows)
    summary["sets_of_triples_that_decide"] = decide_block
    _write_csv(
        out / "unseen.csv",
        ("terms", "filled_triples", "filled_up_to_rewriting", "directions_never_told", "of_which_loops"),
        unseen_rows(plan),
    )
    readings = check_readings(plan, check)
    _write_json(out / "readings.json", readings)
    summary["disagreements"] = check.as_dict()
    summary["every_check_clean"] = check.clean()
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
