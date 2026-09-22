"""Writes `evidence/eleventh/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_eleventh.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on writing.

Cited from the ninth derivation (`ninth.explore`, `ninth.orbits`, `ninth.cost`,
`ninth.reach`) and re-checked by computation
    The eleventh exploration under C-W1 is the ninth's: the results, rounds
    and shortest-sequence counts must agree at the same bound.  Completeness
    within the bound is the ninth's independent count.  Writings are filled
    on every explored result.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ninth.explore import explore as explore_ninth
from ninth.orbits import count_results, two_term_round_count
from ninth.state import DState, empty, written
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from eleventh.changes import first_changes, labeled_of
from eleventh.cost import cost, labeled_cost
from eleventh.explore import (
    Exploration,
    count_shortest_sequences,
    count_shortest_sequences_ninth,
    cycle,
    explore,
    explore_labeled,
    order,
    writings_of,
)
from eleventh.follows import verdicts, writing_verdicts
from eleventh.invariants import WritingCheck, check_writings
from eleventh.state import Labeled, labeled_start
from eleventh.writing import (
    bell,
    coarser_than,
    determines,
    determines_rel,
    injective,
    orbit_count_burnside,
    read_from,
    terms_after_writing,
)

__all__ = [
    "Plan",
    "compare_evidence",
    "compare_with_ninth",
    "count_shortest_sequences",
    "labeled_ok",
    "ninth_ok",
    "run_tag",
    "write_all",
    "write_given",
    "write_labeled",
    "write_run",
    "write_writings",
    "writings_ok",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Under C-W1 the results of round `r` are the ninth's, so the bound is on
    terms and on rounds together as there.  The unchosen labeled reading is
    explored at `labeled_bound` terms and `labeled_rounds` rounds.
    """

    bound: int = 3
    rounds: int = 6
    deep_bound: int = 3
    deep_rounds: int = 5
    two_term_rounds: int = 8
    log_bound: int = 2
    log_rounds: int = 3
    labeled_bound: int = 2
    labeled_rounds: int = 4
    layers_upto: int = 8
    count_upto: int = 3
    count_total_upto: int = 6

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the C-W1 explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def compare_with_ninth(expl: Exploration) -> dict[str, object]:
    """The eleventh's results against the ninth's at the same bound and rounds."""
    ninth = explore_ninth(expl.start, expl.bound, expl.rounds)
    eleventh_keys = set(expl.depth)
    ninth_keys = set(ninth.depth)
    extra = sorted((s.key() for s in eleventh_keys - ninth_keys), key=str)
    missing = sorted((s.key() for s in ninth_keys - eleventh_keys), key=str)
    round_disagreements = [
        s.key() for s in sorted(eleventh_keys & ninth_keys, key=order) if expl.depth[s] != ninth.depth[s]
    ]
    sequences = count_shortest_sequences(expl)
    ninth_seq = count_shortest_sequences_ninth(ninth)
    seq_disagreements = [
        s.key() for s in sorted(eleventh_keys & ninth_keys, key=order) if sequences.get(s) != ninth_seq.get(s)
    ]
    counted = 0
    for n in range(expl.bound + 1):
        degree = expl.rounds - n
        if degree < 0:
            continue
        for c in count_results(n, degree):
            counted += c
    return {
        "ninth_results": len(ninth.depth),
        "eleventh_results": len(expl.depth),
        "same_results": eleventh_keys == ninth_keys,
        "extra_results": extra,
        "missing_results": missing,
        "round_disagreements": round_disagreements,
        "sequence_disagreements": seq_disagreements,
        "explored_equals_independent_count": len(expl.depth) == counted,
        "independent_count": counted,
    }


def ninth_ok(block: dict[str, object]) -> bool:
    """The comparison with the ninth has no disagreement."""
    extra = block["extra_results"]
    missing = block["missing_results"]
    rounds = block["round_disagreements"]
    seq = block["sequence_disagreements"]
    assert isinstance(extra, list) and isinstance(missing, list)
    assert isinstance(rounds, list) and isinstance(seq, list)
    return bool(
        block["same_results"]
        and not extra
        and not missing
        and not rounds
        and not seq
        and block["explored_equals_independent_count"]
    )


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the empty beginning, writings of small states, witnesses."""
    start = empty()
    first = first_changes()
    one = DState.of(1, [], [])
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    apart = (0, 1)
    collide = (0, 0)
    ident = perform_identify(between)
    three_between = DState.of(3, [(0, 1)], [])
    partial = (0, 0, 1)
    collapsed = (0, 0, 0)
    doc: dict[str, object] = {
        "state": written(start),
        "size": start.size,
        "changes": [c.written(start) for c in first],
        "empty_writings": list(writings_of(start)),
        "empty_determines": determines(start, ()),
        "one_term_writing": writings_of(one),
        "one_term_determines": determines(one, (0,)),
        "two_term_empty_injective_determines": determines(two, apart),
        "two_term_empty_collide_determines": determines(two, collide),
        "two_term_between_injective_determines": determines(between, apart),
        "two_term_between_collide_determines": determines(between, collide),
        "two_term_between_collide_determines_r": determines_rel(between, collide, "r"),
        "two_term_between_collide_determines_s": determines_rel(between, collide, "s"),
        "coarser_of_apart_is_collide": coarser_than(apart, collide),
        "apart_is_not_coarser_than_collide": coarser_than(collide, apart),
        "collision_forbids_coarser": (
            not determines(three_between, partial)
            and coarser_than(partial, collapsed)
            and not determines(three_between, collapsed)
        ),
        "injective_is_injective": injective(apart) and not injective(collide),
        "identify_drops_a_term": ident.n == 1,
        "collide_keeps_two_terms": terms_after_writing(between, collide) == 2,
        "read_from_apart": _read_written(read_from(between, apart)),
        "read_from_collide": read_from(between, collide),
        "one_term_cost": cost(one),
        "bell_0_1_2_3": [bell(0), bell(1), bell(2), bell(3)],
        "reaches_itself_in_two_changes": cycle(start) is not None,
        "r_collision_not_s": (not determines_rel(between, collide, "r")) and determines_rel(between, collide, "s"),
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "r_collision_not_s": bool(doc["r_collision_not_s"]),
        "identify_drops_a_term": bool(doc["identify_drops_a_term"]),
        "collide_keeps_two_terms": bool(doc["collide_keeps_two_terms"]),
    }


def perform_identify(state: DState) -> DState:
    """Identify the first two terms of `state`."""
    from ninth.changes import Change, Kind, perform

    return perform(state, Change(Kind.IDENTIFY, "", 0, 1))


def _read_written(read: dict[str, dict[tuple[int, int], int]] | None) -> dict[str, dict[str, int]] | None:
    """JSON-stable form of `read_from`."""
    if read is None:
        return None
    return {rel: {f"{a},{b}": m for (a, b), m in pairs.items()} for rel, pairs in read.items()}


def write_writings(out: Path, expl: Exploration, tag: str) -> dict[str, object]:
    """`writings_<tag>.csv` and the writing check of one exploration."""
    edges = check_writings(expl)
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], s.n, s.key())):
        for writing in writings_of(state):
            rows.append(
                [
                    state.key(),
                    str(writing),
                    int(injective(writing)),
                    int(determines(state, writing)),
                    int(determines_rel(state, writing, "r")),
                    int(determines_rel(state, writing, "s")),
                    expl.depth[state],
                ]
            )
    _write_csv(
        out / f"writings_{tag}.csv",
        ["state", "writing", "injective", "determines", "determines_r", "determines_s", "round"],
        rows,
    )
    return writings_summary(edges)


def writings_summary(edges: WritingCheck) -> dict[str, object]:
    """The writing check as a JSON object.  Disagreement lists empty on correct code."""
    return {
        "checked": edges.checked,
        "injective_writings": edges.injective_writings,
        "determining": edges.determining,
        "colliding": edges.colliding,
        "r_not_s": edges.r_not_s,
        "injective_not_determining": list(edges.injective_not_determining),
        "coarser_of_collision_determines": list(edges.coarser_of_collision_determines),
        "identify_kept_both_terms": list(edges.identify_kept_both_terms),
        "collide_dropped_a_term": list(edges.collide_dropped_a_term),
        "split_agrees": not (
            edges.injective_not_determining
            or edges.coarser_of_collision_determines
            or edges.identify_kept_both_terms
            or edges.collide_dropped_a_term
        ),
    }


def writings_ok(block: dict[str, object]) -> bool:
    """The writing classification of one run has no disagreement."""
    checked = block["checked"]
    assert isinstance(checked, int)
    return bool(
        block["split_agrees"]
        and checked > 0
        and not block["injective_not_determining"]
        and not block["coarser_of_collision_determines"]
        and not block["identify_kept_both_terms"]
        and not block["collide_dropped_a_term"]
    )


def write_run(out: Path, bound: int, rounds: int, plan: Plan, keep_log: bool = False) -> dict[str, object]:
    """One C-W1 exploration: writing classification and the ninth comparison."""
    del plan
    tag = run_tag(bound, rounds)
    expl = explore(empty(), bound, rounds, keep_log=keep_log)
    ninth = compare_with_ninth(expl)
    writings = write_writings(out, expl, tag)
    follows = writing_verdicts(expl)
    state_verdicts = verdicts(expl)
    holding = [v.statement for v in state_verdicts if v.follows_within_bound]
    writing_holding = [v.name for v in follows if v.follows]
    two_term_ok: bool | None
    if bound == 2:
        mismatches = []
        for r, new in enumerate(expl.new_per_round):
            expected = two_term_round_count(r)
            if new != expected:
                mismatches.append(r)
        two_term_ok = not mismatches
    else:
        two_term_ok = None
    row: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_with_a_term": sum(1 for s in expl.depth if s.n >= 1),
        "the_first_round_is_the_one_term_state_alone": (
            expl.new_per_round[1] == 1 if rounds >= 1 else None
        ),
        "empty_changes": len(first_changes()),
        "ninth_derivation": ninth,
        "writings": writings,
        "statements_holding_in_every_result": holding,
        "writing_statements_holding_of_every_writing": writing_holding,
        "two_term_rounds_equal_closed_form": two_term_ok,
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if s.n == 0),
        "results_reached_from_what_is_given": len(expl.depth),
    }
    _write_json(out / f"summary_{tag}.json", row)
    if keep_log:
        from eleventh.explore import performed

        records = [
            {
                "state": state.key(),
                "change": change.written(state),
                "kind": change.kind.value,
                "outcome": outcome.key(),
                "writings": [str(w) for w in writings_of(state)],
                "performed": True,
            }
            for state, change, outcome in performed(expl)
        ]
        (out / f"attempts_{tag}.jsonl").write_text(
            "".join(json.dumps(r, sort_keys=True, ensure_ascii=True) + "\n" for r in records),
            encoding="utf-8",
            newline="\n",
        )
    return row


def write_labeled(out: Path, bound: int, rounds: int) -> dict[str, object]:
    """The unchosen reading C-W2: labeled results, more than the ninth."""
    expl = explore_labeled(bound, rounds)
    ninth = explore_ninth(empty(), bound, rounds)
    two = DState.of(2, [], [])
    apart = Labeled(two, (0, 1))
    collide = Labeled(two, (0, 0))
    extra = len(expl.depth) - len(ninth.depth)
    expected = 0
    for state in ninth.depth:
        expected += orbit_count_burnside(state)
    size_failures = []
    for labeled, depth in expl.depth.items():
        if depth != labeled.size:
            size_failures.append(
                {
                    "state": labeled.state.key(),
                    "writing": str(labeled.writing),
                    "labeled_cost": depth,
                    "size": labeled.size,
                }
            )
    doc: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "labeled_results": len(expl.depth),
        "ninth_results": len(ninth.depth),
        "extra_results": extra,
        "more_results_than_the_ninth": extra > 0,
        "labeled_equals_orbit_count": len(expl.depth) == expected,
        "orbit_count": expected,
        "two_term_empty_apart_cost": labeled_cost(expl, apart),
        "two_term_empty_collide_cost": labeled_cost(expl, collide),
        "two_term_empty_size": two.size,
        "labeled_cost_equals_size": not size_failures,
        "labeled_cost_failures": size_failures[:12],
        "labeled_cost_failure_count": len(size_failures),
        "apart_and_collide_are_two_results": apart != collide,
        "beginning": {"state": labeled_start().state.key(), "writing": list(labeled_start().writing), "cost": 0},
        "labeled_of_two": [list(lab.writing) for lab in labeled_of(two)],
    }
    _write_json(out / "labeled.json", doc)
    return doc


def labeled_ok(block: dict[str, object]) -> bool:
    """C-W2 has extra results; cost of a labeled result is still the size."""
    return bool(
        block["more_results_than_the_ninth"]
        and block["labeled_equals_orbit_count"]
        and block["labeled_cost_equals_size"]
        and block["two_term_empty_apart_cost"] == block["two_term_empty_size"] == 2
        and block["two_term_empty_collide_cost"] == 2
        and block["apart_and_collide_are_two_results"]
    )


def write_all(out: Path, plan: Plan | None = None) -> dict[str, object]:
    """Every computed file of `evidence/eleventh/`."""
    plan = plan or Plan()
    out.mkdir(parents=True, exist_ok=True)
    given = write_given(out)
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan, keep_log=False)
    log = write_run(out, plan.log_bound, plan.log_rounds, plan, keep_log=True)
    runs[run_tag(plan.log_bound, plan.log_rounds) + "_log"] = log
    labeled = write_labeled(out, plan.labeled_bound, plan.labeled_rounds)
    summary = {
        "plan": {
            "bound": plan.bound,
            "rounds": plan.rounds,
            "deep_bound": plan.deep_bound,
            "deep_rounds": plan.deep_rounds,
            "two_term_rounds": plan.two_term_rounds,
            "log_bound": plan.log_bound,
            "log_rounds": plan.log_rounds,
            "labeled_bound": plan.labeled_bound,
            "labeled_rounds": plan.labeled_rounds,
        },
        "given": given,
        "runs": runs,
        "labeled": labeled,
        "reading": "C-W1 writing on the result as a reading; C-W2 writing in the result, unchosen, kept",
    }
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
