"""Writes `evidence/tenth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_tenth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on leftover.

Cited from the ninth derivation (`ninth.explore`, `ninth.orbits`, `ninth.cost`,
`ninth.reach`) and re-checked by computation
    The tenth exploration under C-L1 is the ninth's: the results, rounds and
    shortest-sequence counts must agree at the same bound.  Completeness
    within the bound is the ninth's independent count.  Leftover is filled
    on every performed change.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ninth.explore import explore as explore_ninth
from ninth.orbits import count_results, two_term_round_count
from ninth.state import DState, empty, written
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from tenth.changes import Change, Kind, first_changes, is_addition, leftover_counts, other_clears
from tenth.cost import cost, tagged_cost
from tenth.explore import (
    Exploration,
    TaggedExploration,
    attempt,
    count_shortest_sequences,
    count_shortest_sequences_ninth,
    cycle,
    explore,
    explore_tagged,
    leftover_performed,
    order,
)
from tenth.follows import leftover_verdicts, verdicts
from tenth.invariants import LeftoverCheck, check_leftovers
from tenth.leftover import LeftOver, leftover_of, restores_in_one
from tenth.state import Tagged, tagged_start

__all__ = [
    "Plan",
    "compare_evidence",
    "compare_with_ninth",
    "count_shortest_sequences",
    "leftover_of",
    "ninth_ok",
    "run_tag",
    "tagged_ok",
    "write_all",
    "write_given",
    "write_leftovers",
    "write_run",
    "write_tagged",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Under C-L1 the results of round `r` are the ninth's, so the bound is on
    terms and on rounds together as there.  The unchosen tagged reading is
    explored at `tagged_bound` terms and `tagged_rounds` rounds.
    """

    bound: int = 3
    rounds: int = 6
    deep_bound: int = 3
    deep_rounds: int = 5
    two_term_rounds: int = 8
    log_bound: int = 2
    log_rounds: int = 3
    tagged_bound: int = 2
    tagged_rounds: int = 4
    layers_upto: int = 8
    count_upto: int = 3
    count_total_upto: int = 6

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the C-L1 explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def compare_with_ninth(expl: Exploration) -> dict[str, object]:
    """The tenth's results against the ninth's at the same bound and rounds."""
    ninth = explore_ninth(expl.start, expl.bound, expl.rounds)
    tenth_keys = set(expl.depth)
    ninth_keys = set(ninth.depth)
    extra = sorted((s.key() for s in tenth_keys - ninth_keys), key=str)
    missing = sorted((s.key() for s in ninth_keys - tenth_keys), key=str)
    round_disagreements = [
        s.key() for s in sorted(tenth_keys & ninth_keys, key=order) if expl.depth[s] != ninth.depth[s]
    ]
    sequences = count_shortest_sequences(expl)
    ninth_seq = count_shortest_sequences_ninth(ninth)
    seq_disagreements = [
        s.key() for s in sorted(tenth_keys & ninth_keys, key=order) if sequences.get(s) != ninth_seq.get(s)
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
        "tenth_results": len(expl.depth),
        "same_results": tenth_keys == ninth_keys,
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
    """`given.json`: the empty beginning, leftover of its one change, witnesses for the three outcomes."""
    start = empty()
    first = first_changes()
    rec = attempt(start, first[0], bound=2)
    one = DState.of(1, [], [])
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    identify_two = Change(Kind.IDENTIFY, "", 0, 1)
    remove_ara = Change(Kind.REMOVE, "r", 0, 0)
    ara = DState.of(1, [(0, 0)], [])
    doc: dict[str, object] = {
        "state": written(start),
        "size": start.size,
        "changes": [c.written(start) for c in first],
        "leftover_of_the_first_change": leftover_of(start, first[0]).value,
        "the_first_change_leaves_nothing": leftover_of(start, first[0]) is LeftOver.NOTHING_LEFT,
        "outcome_of_the_first_change": None if rec.outcome is None else written(rec.outcome),
        "one_term_cost": cost(one),
        "two_term_empty_identify_leftover": leftover_of(two, identify_two).value,
        "two_term_empty_identify_restored_in_one": restores_in_one(two, identify_two),
        "two_term_between_identify_leftover": leftover_of(between, identify_two).value,
        "two_term_between_identify_restored_in_one": restores_in_one(between, identify_two),
        "remove_ara_leftover": leftover_of(ara, remove_ara).value,
        "other_relation_clears_a_removal": other_clears(ara, remove_ara),
        "reaches_itself_in_two_changes": cycle(start) is not None,
        "three_outcomes_inhabited": {
            leftover_of(start, first[0]),
            leftover_of(ara, remove_ara),
            leftover_of(between, identify_two),
        }
        == set(LeftOver),
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "leftover_of_the_first_change": leftover_of(start, first[0]).value,
        "three_outcomes_inhabited": bool(doc["three_outcomes_inhabited"]),
    }


def write_leftovers(out: Path, expl: Exploration, tag: str) -> dict[str, object]:
    """`leftovers_<tag>.csv` and the leftover check of one exploration."""
    edges = check_leftovers(expl)
    rows: list[list[object]] = []
    for state, change, arrived, leftover in leftover_performed(expl):
        rows.append(
            [
                state.key(),
                change.written(state),
                change.kind.value,
                change.rel or "",
                leftover.value,
                arrived.key(),
                int(is_addition(change)),
            ]
        )
    _write_csv(
        out / f"leftovers_{tag}.csv",
        ["state", "change", "kind", "relation", "leftover", "outcome", "is_addition"],
        rows,
    )
    return leftover_summary(edges)


def leftover_summary(edges: LeftoverCheck) -> dict[str, object]:
    """The leftover check as a JSON object.  Disagreement lists empty on correct code."""
    return {
        "checked": edges.checked,
        "nothing_left": edges.nothing_left,
        "clearable": edges.clearable,
        "uncleared": edges.uncleared,
        "three_outcomes_inhabited": edges.nothing_left > 0 and edges.clearable > 0 and edges.uncleared > 0,
        "additions_not_nothing": list(edges.additions_not_nothing),
        "removals_not_clearable": list(edges.removals_not_clearable),
        "other_relation_cleared": list(edges.other_relation_cleared),
        "identify_disagreements": list(edges.identify_disagreements),
        "clearing_failed": list(edges.clearing_failed),
        "split_agrees": not (
            edges.additions_not_nothing
            or edges.removals_not_clearable
            or edges.other_relation_cleared
            or edges.identify_disagreements
            or edges.clearing_failed
        ),
    }


def leftovers_ok(block: dict[str, object]) -> bool:
    """The leftover classification of one run has no disagreement.

    All three outcomes are inhabited once the bound and rounds hold a
    two-term state with an assertion between the terms (round 4); smaller
    runs may see only additions and removals, or only additions.
    """
    checked = block["checked"]
    assert isinstance(checked, int)
    return bool(
        block["split_agrees"]
        and checked > 0
        and not block["additions_not_nothing"]
        and not block["removals_not_clearable"]
        and not block["other_relation_cleared"]
        and not block["identify_disagreements"]
        and not block["clearing_failed"]
    )


def write_run(out: Path, bound: int, rounds: int, plan: Plan, keep_log: bool = False) -> dict[str, object]:
    """One C-L1 exploration: leftover classification and the ninth comparison."""
    del plan
    tag = run_tag(bound, rounds)
    expl = explore(empty(), bound, rounds, keep_log=keep_log)
    ninth = compare_with_ninth(expl)
    leftovers = write_leftovers(out, expl, tag)
    follows = leftover_verdicts(expl)
    state_verdicts = verdicts(expl)
    holding = [v.statement for v in state_verdicts if v.follows_within_bound]
    leftover_holding = [v.name for v in follows if v.follows]
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
    counts = leftover_counts(empty())
    row: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_with_a_term": sum(1 for s in expl.depth if s.n >= 1),
        "the_first_round_is_the_one_term_state_alone": (
            expl.new_per_round[1] == 1 if rounds >= 1 else None
        ),
        "empty_changes": counts[0],
        "empty_nothing_left": counts[1],
        "ninth_derivation": ninth,
        "leftovers": leftovers,
        "statements_holding_in_every_result": holding,
        "leftover_statements_holding_of_every_change": leftover_holding,
        "two_term_rounds_equal_closed_form": two_term_ok,
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if s.n == 0),
        "results_reached_from_what_is_given": len(expl.depth),
    }
    _write_json(out / f"summary_{tag}.json", row)
    if keep_log:
        records = []
        for rec in expl.log:
            records.append(
                {
                    "state": rec.state.key(),
                    "change": rec.change.written(rec.state),
                    "kind": rec.change.kind.value,
                    "leftover": rec.leftover.value,
                    "outcome": None if rec.outcome is None else rec.outcome.key(),
                    "beyond_bound": rec.beyond,
                    "performed": True,
                }
            )
        (out / f"attempts_{tag}.jsonl").write_text(
            "".join(json.dumps(r, sort_keys=True, ensure_ascii=True) + "\n" for r in records),
            encoding="utf-8",
            newline="\n",
        )
    return row


def write_tagged(out: Path, bound: int, rounds: int) -> dict[str, object]:
    """The unchosen reading C-L2: tagged results, cost not the size."""
    expl = explore_tagged(bound, rounds)
    ninth = explore_ninth(empty(), bound, rounds)
    one = DState.of(1, [], [])
    clearable_one = Tagged(one, LeftOver.CLEARABLE)
    nothing_one = Tagged(one, LeftOver.NOTHING_LEFT)
    extra = len(expl.depth) - len(ninth.depth)
    size_failures = []
    for tagged, depth in expl.depth.items():
        if depth != tagged.size:
            size_failures.append({"state": tagged.state.key(), "leftover": tagged.leftover.value, "tagged_cost": depth, "size": tagged.size})
    # keep a bounded witness list
    size_failures_head = size_failures[:12]
    doc: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "tagged_results": len(expl.depth),
        "ninth_results": len(ninth.depth),
        "extra_results": extra,
        "more_results_than_the_ninth": extra > 0,
        "one_term_nothing_left_cost": tagged_cost(expl, nothing_one),
        "one_term_clearable_cost": tagged_cost(expl, clearable_one),
        "one_term_size": one.size,
        "tagged_cost_exceeds_size": bool(size_failures),
        "tagged_cost_failures": size_failures_head,
        "tagged_cost_failure_count": len(size_failures),
        "beginning": {"state": tagged_start().state.key(), "leftover": tagged_start().leftover.value, "cost": 0},
    }
    _write_json(out / "tagged.json", doc)
    return doc


def tagged_ok(block: dict[str, object]) -> bool:
    """C-L2 has extra results and a cost that is not the size."""
    return bool(
        block["more_results_than_the_ninth"]
        and block["tagged_cost_exceeds_size"]
        and block["one_term_nothing_left_cost"] == block["one_term_size"] == 1
        and block["one_term_clearable_cost"] is not None
        and int(str(block["one_term_clearable_cost"])) > 1
    )


def write_all(out: Path, plan: Plan | None = None) -> dict[str, object]:
    """Every computed file of `evidence/tenth/`."""
    plan = plan or Plan()
    out.mkdir(parents=True, exist_ok=True)
    given = write_given(out)
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan, keep_log=False)
    log = write_run(out, plan.log_bound, plan.log_rounds, plan, keep_log=True)
    runs[run_tag(plan.log_bound, plan.log_rounds) + "_log"] = log
    tagged = write_tagged(out, plan.tagged_bound, plan.tagged_rounds)
    summary = {
        "plan": {
            "bound": plan.bound,
            "rounds": plan.rounds,
            "deep_bound": plan.deep_bound,
            "deep_rounds": plan.deep_rounds,
            "two_term_rounds": plan.two_term_rounds,
            "log_bound": plan.log_bound,
            "log_rounds": plan.log_rounds,
            "tagged_bound": plan.tagged_bound,
            "tagged_rounds": plan.tagged_rounds,
        },
        "given": given,
        "runs": runs,
        "tagged": tagged,
        "reading": "C-L1 leftover on the change; C-L2 leftover in the result, unchosen, kept",
    }
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
