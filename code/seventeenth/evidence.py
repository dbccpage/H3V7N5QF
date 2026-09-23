"""Checks and the regenerable files of `evidence/seventeenth/`.

Each list below is empty on the derivation as it stands, and names a
disagreement between two computations that do not call each other:

* the A-replace closure against `xry.explore`;
* that closure against the base cost, state by state and as a set;
* the A-perform closure against the one-step witnesses;
* M1 against M2, on loop-free states and on the loopy witness;
* the base answer "remove the obstruction" against perform-then-remove;
* a refusal against the state it was refused on.

The frontier has two kinds of entry: `|terms`, an attempt whose outcome has
more terms than the bound, and `|rounds`, a result first reached in the last
round, whose changes the round bound left unattempted. `results_*.csv`
records, for every result, what it adds to what is given.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, fields
from pathlib import Path

from xry.changes import AnswerKind, Change, Kind, answers, changes, perform
from xry.cost import cost
from xry.evidence import _write_csv, compare_evidence, write_manifest
from xry.explore import explore, order
from xry.state import Sameness, State, added, canonical, given

from seventeenth.explore import (
    by_cost,
    closure_perform,
    closure_unobstructed,
    identified,
    loopy_witness,
    with_loop,
    with_other_loop,
)
from seventeenth.loop import has_xrx, obstructed_m1, outcome_has_xrx


@dataclass
class LoopCheck:
    """Disagreements of one bounded check. Empty lists are the passing check."""

    replace_has_xrx: list[str]
    replace_not_base: list[str]
    replace_cost_mismatch: list[str]
    replace_not_formula: list[str]
    perform_misses_witness: list[str]
    perform_cost_not_above: list[str]
    m_disagree_loopfree: list[str]
    m_agree_on_loop: list[str]
    remove_first_differs: list[str]
    refusal_changes_something: list[str]
    loop_beginning_in_replace: list[str]
    loop_beginning_not_in_perform: list[str]
    replace_results: int
    perform_results: int
    frontier: tuple[str, ...] = ()
    by_run: tuple[str, ...] = ()
    unexpanded_by_run: tuple[str, ...] = ()


def disagreements(report: LoopCheck) -> dict[str, list[str]]:
    """Every disagreement list of `report`, by field name."""
    return {
        field.name: getattr(report, field.name)
        for field in fields(report)
        if isinstance(getattr(report, field.name), list)
    }


def _depth_diff(left: dict[State, int], right: dict[State, int]) -> list[str]:
    """Keys where `left` and `right` disagree, in `State.key` order."""
    bad = [state.key() for state in set(left) | set(right) if left.get(state) != right.get(state)]
    return sorted(bad)


def _runs() -> tuple[tuple[bool, Sameness], ...]:
    """The four runs: `bra` asserted or not, under both readings of sameness."""
    return tuple((bra, sameness) for bra in (False, True) for sameness in Sameness)


def check_bounds(bound: int, rounds: int) -> LoopCheck:
    """Run both readings at one bound. Disagreement lists are sorted."""
    replace_has: list[str] = []
    not_base: list[str] = []
    cost_bad: list[str] = []
    not_formula: list[str] = []
    misses: list[str] = []
    not_above: list[str] = []
    disagree: list[str] = []
    agree_loop: list[str] = []
    remove_differs: list[str] = []
    refusal_bad: list[str] = []
    begin_in: list[str] = []
    begin_out: list[str] = []
    replace_n = 0
    perform_n = 0
    frontier: list[str] = []
    by_run: list[str] = []
    unexpanded: list[str] = []
    for bra, sameness in _runs():
        start = given(bra, sameness)
        tag = f"{sameness.value}/{bra}"
        replace = closure_unobstructed(start, bound, rounds)
        performed = closure_perform(start, bound, rounds)
        base = explore(start, bound, rounds)
        frontier.extend(f"{tag}:replace:{item}" for item in replace.frontier)
        frontier.extend(f"{tag}:perform:{item}" for item in performed.frontier)
        frontier.extend(f"{tag}:replace:{key}|rounds" for key in replace.unexpanded)
        frontier.extend(f"{tag}:perform:{key}|rounds" for key in performed.unexpanded)
        replace_n += len(replace.depth)
        perform_n += len(performed.depth)
        by_run.append(f"{tag}:replace:{len(replace.depth)}:perform:{len(performed.depth)}")
        unexpanded.append(f"{tag}:replace:{len(replace.unexpanded)}:perform:{len(performed.unexpanded)}")
        for state in replace.depth:
            if has_xrx(state):
                replace_has.append(f"{tag}:{state.key()}")
            if cost(state, bra) != replace.depth[state]:
                cost_bad.append(f"{tag}:{state.key()}")
        not_base.extend(f"{tag}:{key}" for key in _depth_diff(base.depth, replace.depth))
        formula = by_cost(bound, rounds, bra, sameness)
        not_formula.extend(f"{tag}:{key}" for key in _depth_diff({s: 0 for s in formula}, {s: 0 for s in replace.depth}))
        witness = identified(bra, sameness)
        length = performed.depth.get(witness)
        if length is None:
            misses.append(f"{tag}:{witness.key()}")
        elif cost(witness, bra) <= length:
            not_above.append(f"{tag}:{witness.key()}")
        for state in replace.depth:
            for change in changes(state):
                if obstructed_m1(state, change) != outcome_has_xrx(state, change):
                    disagree.append(f"{tag}:{state.key()}:{change.written(state)}")
        for begin in (with_loop(bra, sameness), with_other_loop(bra, sameness)):
            if begin in replace.depth:
                begin_in.append(f"{tag}:{begin.key()}")
            if begin not in performed.depth:
                begin_out.append(f"{tag}:{begin.key()}")
        if _remove_first_differs(bra, sameness):
            remove_differs.append(tag)
        if _refusal_changes(bra, sameness):
            refusal_bad.append(tag)
    loop_state, loop_change = loopy_witness()
    if obstructed_m1(loop_state, loop_change) == outcome_has_xrx(loop_state, loop_change):
        agree_loop.append(f"{loop_state.key()}:{loop_change.written(loop_state)}")
    return LoopCheck(
        sorted(replace_has),
        sorted(not_base),
        sorted(cost_bad),
        sorted(not_formula),
        sorted(misses),
        sorted(not_above),
        sorted(disagree),
        sorted(agree_loop),
        sorted(remove_differs),
        sorted(refusal_bad),
        sorted(begin_in),
        sorted(begin_out),
        replace_n,
        perform_n,
        tuple(sorted(set(frontier))),
        tuple(by_run),
        tuple(unexpanded),
    )


def _remove_first_differs(bra: bool, sameness: Sameness) -> bool:
    """Perform-then-remove and the base's remove-then-perform end apart."""
    start = given(bra, sameness)
    identify = Change(Kind.IDENTIFY, 0, 1)
    removals = [answer for answer in answers(start, identify) if answer.kind is AnswerKind.REMOVE_OBSTRUCTION]
    mid = perform(start, identify)
    # The merged assertion is `ara` on the one term the identification writes as 0.
    after = canonical(perform(mid, Change(Kind.REMOVE, 0, 0)))
    if not removals:
        return True
    return canonical(removals[0].result) != after


def _refusal_changes(bra: bool, sameness: Sameness) -> bool:
    """The refusal of adding `ara` changes the state, or is not there."""
    start = given(bra, sameness)
    refused = [
        answer
        for answer in answers(start, Change(Kind.ADD_ASSERTION, 0, 0))
        if answer.kind is AnswerKind.REFUSE
    ]
    if len(refused) != 1:
        return True
    return refused[0].result != start or refused[0].completes


def passes(report: LoopCheck) -> bool:
    """Every disagreement list is empty."""
    return not any(disagreements(report).values())


RESULT_HEADER = (
    "run",
    "reading",
    "state",
    "written",
    "terms",
    "assertions",
    "terms_added_to_given",
    "assertions_added_to_given",
    "round_first_reached",
    "asserts_xrx",
)


def result_rows(bound: int, rounds: int) -> list[list[object]]:
    """One row per result of each run and reading: what it adds to what is given, and when."""
    rows: list[list[object]] = []
    for bra, sameness in _runs():
        start = given(bra, sameness)
        tag = f"{sameness.value}/{bra}"
        for reading, closed in (
            ("replace", closure_unobstructed(start, bound, rounds)),
            ("perform", closure_perform(start, bound, rounds)),
        ):
            for state in sorted(closed.depth, key=lambda s: (closed.depth[s], order(s))):
                terms, assertions = added(state)
                rows.append(
                    [
                        tag,
                        reading,
                        state.key(),
                        state.written(),
                        state.n,
                        state.m,
                        terms,
                        assertions,
                        closed.depth[state],
                        int(has_xrx(state)),
                    ]
                )
    return rows


@dataclass(frozen=True)
class Plan:
    """Bounds written into `evidence/seventeenth/`. Small enough to regenerate."""

    bound: int = 3
    rounds: int = 6
    log_bound: int = 2
    log_rounds: int = 3


def write_all(out: Path, plan: Plan | None = None) -> dict[str, object]:
    """Write `summary.json`, the result rows, and the small attempt log. Return the summary."""
    chosen = plan or Plan()
    out.mkdir(parents=True, exist_ok=True)
    report = check_bounds(chosen.bound, chosen.rounds)
    summary: dict[str, object] = {
        "bound": chosen.bound,
        "rounds": chosen.rounds,
        "passes": passes(report),
        "runs": len(_runs()),
        "replace_results_summed_over_runs": report.replace_results,
        "perform_results_summed_over_runs": report.perform_results,
        "frontier": list(report.frontier),
        "by_run": list(report.by_run),
        "unexpanded_by_run": list(report.unexpanded_by_run),
    }
    summary.update(disagreements(report))
    (out / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    results_name = f"results_bound{chosen.bound}_rounds{chosen.rounds}.csv"
    _write_csv(out / results_name, RESULT_HEADER, result_rows(chosen.bound, chosen.rounds))
    lines: list[str] = []
    for bra, sameness in _runs():
        start = given(bra, sameness)
        for run in (
            closure_unobstructed(start, chosen.log_bound, chosen.log_rounds, keep_log=True),
            closure_perform(start, chosen.log_bound, chosen.log_rounds, keep_log=True),
        ):
            for record in run.log:
                lines.append(
                    json.dumps(
                        {
                            "bra": bra,
                            "change": record.change,
                            "entered": record.entered,
                            "obstructed": record.obstructed,
                            "outcome": record.outcome,
                            "reading": record.reading,
                            "round": record.round,
                            "sameness": sameness.value,
                            "state": record.state,
                        },
                        sort_keys=True,
                    )
                )
    log_name = f"attempts_bound{chosen.log_bound}_rounds{chosen.log_rounds}.jsonl"
    (out / log_name).write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    write_manifest(out)
    return summary
