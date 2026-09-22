"""Writes `evidence/fourteenth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_fourteenth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on leftover.

Cited from the ninth derivation (`ninth.explore`, `ninth.orbits`, `ninth.cost`,
`ninth.reach`) and re-checked by computation
    The fourteenth exploration under C-F1 is the ninth's: the results, rounds
    and shortest-sequence counts must agree at the same bound.  Completeness
    within the bound is the ninth's independent count.  Leftover writing is
    filled on every performed change.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ninth.changes import Change, Kind, first_changes
from ninth.explore import explore as explore_ninth
from ninth.orbits import count_results, two_term_round_count
from ninth.state import DState, empty, written
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from fourteenth.changes import leftover_counts
from fourteenth.cost import cost, tagged_cost
from fourteenth.explore import (
    Exploration,
    attempt,
    count_shortest_sequences,
    count_shortest_sequences_ninth,
    cycle,
    explore,
    explore_tagged,
    leftover_performed,
    order,
)
from fourteenth.follows import leftover_verdicts, verdicts
from fourteenth.invariants import LeftoverCheck, check_leftovers
from fourteenth.leftover import leftover_merge, leftover_nothing, leftover_of, leftover_pair
from fourteenth.state import Tagged, tagged_start

__all__ = [
    "Plan",
    "compare_evidence",
    "compare_with_ninth",
    "count_shortest_sequences",
    "leftover_of",
    "leftovers_ok",
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

    Under C-F1 the results of round `r` are the ninth's, so the bound is on
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
    tagged_rounds: int = 5
    layers_upto: int = 8
    count_upto: int = 3
    count_total_upto: int = 6

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the C-F1 explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def compare_with_ninth(expl: Exploration) -> dict[str, object]:
    """The fourteenth's results against the ninth's at the same bound and rounds."""
    ninth = explore_ninth(expl.start, expl.bound, expl.rounds)
    fourteenth_keys = set(expl.depth)
    ninth_keys = set(ninth.depth)
    extra = sorted((s.key() for s in fourteenth_keys - ninth_keys), key=str)
    missing = sorted((s.key() for s in ninth_keys - fourteenth_keys), key=str)
    round_disagreements = [
        s.key() for s in sorted(fourteenth_keys & ninth_keys, key=order) if expl.depth[s] != ninth.depth[s]
    ]
    sequences = count_shortest_sequences(expl)
    ninth_seq = count_shortest_sequences_ninth(ninth)
    seq_disagreements = [
        s.key() for s in sorted(fourteenth_keys & ninth_keys, key=order) if sequences.get(s) != ninth_seq.get(s)
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
        "fourteenth_results": len(expl.depth),
        "same_results": fourteenth_keys == ninth_keys,
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
    """`given.json`: the empty beginning, leftover of its one change, witnesses."""
    start = empty()
    first = first_changes()
    rec = attempt(start, first[0], bound=2)
    one = DState.of(1, [], [])
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    # `0 r 1` and `0 s 1` both asserted, so removing the pair is a legal change
    # in either relation — the D5 witness needs two real changes, not one
    # change and a non-change.
    between_both = DState.of(2, [(0, 1)], [(0, 1)])
    identify_two = Change(Kind.IDENTIFY, "", 0, 1)
    remove_r = Change(Kind.REMOVE, "r", 0, 1)
    remove_s = Change(Kind.REMOVE, "s", 0, 1)
    ara = DState.of(1, [(0, 0)], [])
    remove_ara = Change(Kind.REMOVE, "r", 0, 0)
    remove_asa = Change(Kind.REMOVE, "s", 0, 0)
    both = DState.of(1, [(0, 0)], [(0, 0)])
    first_leftover = leftover_of(start, first[0])
    r_leftover = leftover_of(between_both, remove_r)
    s_leftover = leftover_of(between_both, remove_s)
    assert between_both.has("r", 0, 1) and between_both.has("s", 0, 1)
    doc: dict[str, object] = {
        "state": written(start),
        "size": start.size,
        "changes": [c.written(start) for c in first],
        "leftover_of_the_first_change": first_leftover.written(),
        "the_first_change_leaves_nothing": first_leftover.kind == "nothing",
        "first_leftover_is_assertion": first_leftover.is_assertion(),
        "first_leftover_is_answer": first_leftover.is_answer(),
        "first_leftover_is_xry": first_leftover.is_xry(),
        "first_leftover_is_xsy": first_leftover.is_xsy(),
        "outcome_of_the_first_change": None if rec.outcome is None else written(rec.outcome),
        "one_term_cost": cost(one),
        "two_term_empty_identify_leftover": leftover_of(two, identify_two).written(),
        "two_term_between_identify_leftover": leftover_of(between, identify_two).written(),
        "remove_r_leftover": r_leftover.written(),
        "remove_s_leftover": s_leftover.written(),
        "r_and_s_same_leftover": r_leftover == s_leftover,
        "r_leftover_is_assertion": r_leftover.is_assertion(),
        "remove_ara_leftover": leftover_of(ara, remove_ara).written(),
        "remove_asa_on_both_leftover": leftover_of(both, remove_asa).written(),
        "ara_and_asa_same_leftover": leftover_of(both, remove_ara) == leftover_of(both, remove_asa),
        "reaches_itself_in_two_changes": cycle(start) is not None,
        "empty_changes": len(first),
        "pair_written_uses_neither_r_nor_s": r_leftover.written() == "0ℓ1",
        "merge_written_is_not_assertion": leftover_merge(0, 1).written() == "0∼1",
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "leftover_of_the_first_change": first_leftover.written(),
        "r_and_s_same_leftover": bool(doc["r_and_s_same_leftover"]),
        "leftover_not_assertion": not bool(doc["r_leftover_is_assertion"]) and not bool(doc["first_leftover_is_assertion"]),
        "leftover_not_answer": not bool(doc["first_leftover_is_answer"]),
    }


def write_leftovers(out: Path, expl: Exploration, tag: str) -> dict[str, object]:
    """`leftovers_<tag>.csv` and the leftover check of one exploration."""
    edges = check_leftovers(expl)
    rows: list[list[object]] = []
    for state, change, arrived, writing in leftover_performed(expl):
        rows.append(
            [
                state.key(),
                change.written(state),
                change.kind.value,
                change.rel or "",
                writing.written(),
                writing.kind,
                arrived.key(),
                int(writing.is_assertion()),
            ]
        )
    _write_csv(
        out / f"leftovers_{tag}.csv",
        ["state", "change", "kind", "relation", "leftover", "leftover_kind", "outcome", "is_assertion"],
        rows,
    )
    return leftover_summary(edges)


def leftover_summary(edges: LeftoverCheck) -> dict[str, object]:
    """The leftover check as a JSON object.  Disagreement lists empty on correct code."""
    return {
        "checked": edges.checked,
        "nothing": edges.nothing,
        "pair": edges.pair,
        "merge": edges.merge,
        "three_kinds_inhabited": edges.nothing > 0 and edges.pair > 0 and edges.merge > 0,
        "additions_not_nothing": list(edges.additions_not_nothing),
        "removals_not_pair": list(edges.removals_not_pair),
        "identify_not_merge": list(edges.identify_not_merge),
        "assertion_writings": list(edges.assertion_writings),
        "answer_writings": list(edges.answer_writings),
        "clearing_kind": list(edges.clearing_kind),
        "cross_relation_disagree": list(edges.cross_relation_disagree),
        "split_agrees": not (
            edges.additions_not_nothing
            or edges.removals_not_pair
            or edges.identify_not_merge
            or edges.assertion_writings
            or edges.answer_writings
            or edges.clearing_kind
            or edges.cross_relation_disagree
        ),
    }


def leftovers_ok(block: dict[str, object]) -> bool:
    """The leftover classification of one run has no disagreement."""
    checked = block["checked"]
    assert isinstance(checked, int)
    if checked == 0:
        return True
    return bool(
        block["split_agrees"]
        and not block["additions_not_nothing"]
        and not block["removals_not_pair"]
        and not block["identify_not_merge"]
        and not block["assertion_writings"]
        and not block["answer_writings"]
        and not block["clearing_kind"]
        and not block["cross_relation_disagree"]
    )


def write_run(out: Path, bound: int, rounds: int, plan: Plan, keep_log: bool = False) -> dict[str, object]:
    """One C-F1 exploration: leftover classification and the ninth comparison."""
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
        "empty_nothing": counts[1],
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
                    "leftover": rec.leftover.written(),
                    "leftover_kind": rec.leftover.kind,
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
    """The unchosen reading C-F2: tagged results, cost not the size."""
    expl = explore_tagged(bound, rounds)
    ninth = explore_ninth(empty(), bound, rounds)
    one = DState.of(1, [], [])
    pair_one = Tagged(one, leftover_pair(0, 0))
    nothing_one = Tagged(one, leftover_nothing())
    extra = len(expl.depth) - len(ninth.depth)
    size_failures = []
    for tagged, depth in expl.depth.items():
        if depth != tagged.size:
            size_failures.append(
                {
                    "state": tagged.state.key(),
                    "leftover": tagged.leftover.written(),
                    "tagged_cost": depth,
                    "size": tagged.size,
                }
            )
    size_failures_head = size_failures[:12]
    doc: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "tagged_results": len(expl.depth),
        "ninth_results": len(ninth.depth),
        "extra_results": extra,
        "more_results_than_the_ninth": extra > 0,
        "one_term_nothing_cost": tagged_cost(expl, nothing_one),
        "one_term_pair_cost": tagged_cost(expl, pair_one),
        "one_term_size": one.size,
        "tagged_cost_exceeds_size": bool(size_failures),
        "tagged_cost_failures": size_failures_head,
        "tagged_cost_failure_count": len(size_failures),
        "beginning": {
            "state": tagged_start().state.key(),
            "leftover": tagged_start().leftover.written(),
            "cost": 0,
        },
    }
    _write_json(out / "tagged.json", doc)
    return doc


def tagged_ok(block: dict[str, object]) -> bool:
    """C-F2 has extra results and a cost that is not the size."""
    pair_cost = block["one_term_pair_cost"]
    return bool(
        block["more_results_than_the_ninth"]
        and block["tagged_cost_exceeds_size"]
        and block["one_term_nothing_cost"] == block["one_term_size"] == 1
        and pair_cost is not None
        and int(str(pair_cost)) > 1
    )


def write_all(out: Path, plan: Plan | None = None) -> dict[str, object]:
    """Every computed file of `evidence/fourteenth/`."""
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
        "reading": "C-F1 leftover writing on the change; C-F2 leftover writing in the result, unchosen, kept",
    }
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
