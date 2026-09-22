"""Writes `evidence/twelfth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_twelfth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on the identification record.

Cited from the ninth derivation (`ninth.explore`, `ninth.orbits`, `ninth.cost`,
`ninth.reach`) and re-checked by computation
    The twelfth exploration under C-M1 is the ninth's: the results, rounds
    and shortest-sequence counts must agree at the same bound.  Completeness
    within the bound is the ninth's independent count.  Identification
    records are filled on every identification.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ninth.changes import Change, Kind, perform
from ninth.explore import explore as explore_ninth
from ninth.orbits import count_results, two_term_round_count
from ninth.state import DState, empty, written
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from twelfth.changes import first_changes
from twelfth.cost import cost, recorded_cost
from twelfth.explore import (
    Exploration,
    count_shortest_sequences,
    count_shortest_sequences_ninth,
    cycle,
    explore,
    explore_recorded,
    order,
    performed,
)
from twelfth.follows import record_verdicts, verdicts
from twelfth.invariants import RecordCheck, check_records
from twelfth.record import record_determined_by_rel, record_of, restores_listed
from twelfth.state import Recorded, recorded_start

__all__ = [
    "Plan",
    "compare_evidence",
    "compare_with_ninth",
    "count_shortest_sequences",
    "ninth_ok",
    "recorded_ok",
    "records_ok",
    "run_tag",
    "write_all",
    "write_given",
    "write_recorded",
    "write_records",
    "write_run",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Under C-M1 the results of round `r` are the ninth's, so the bound is on
    terms and on rounds together as there.  The unchosen recorded reading is
    explored at `recorded_bound` terms and `recorded_rounds` rounds.
    """

    bound: int = 3
    rounds: int = 6
    deep_bound: int = 3
    deep_rounds: int = 5
    two_term_rounds: int = 8
    log_bound: int = 2
    log_rounds: int = 3
    recorded_bound: int = 2
    recorded_rounds: int = 5
    layers_upto: int = 8
    count_upto: int = 3
    count_total_upto: int = 6

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the C-M1 explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def compare_with_ninth(expl: Exploration) -> dict[str, object]:
    """The twelfth's results against the ninth's at the same bound and rounds."""
    ninth = explore_ninth(expl.start, expl.bound, expl.rounds)
    twelfth_keys = set(expl.depth)
    ninth_keys = set(ninth.depth)
    extra = sorted((s.key() for s in twelfth_keys - ninth_keys), key=str)
    missing = sorted((s.key() for s in ninth_keys - twelfth_keys), key=str)
    round_disagreements = [
        s.key() for s in sorted(twelfth_keys & ninth_keys, key=order) if expl.depth[s] != ninth.depth[s]
    ]
    sequences = count_shortest_sequences(expl)
    ninth_seq = count_shortest_sequences_ninth(ninth)
    seq_disagreements = [
        s.key() for s in sorted(twelfth_keys & ninth_keys, key=order) if sequences.get(s) != ninth_seq.get(s)
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
        "twelfth_results": len(expl.depth),
        "same_results": twelfth_keys == ninth_keys,
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
    """`given.json`: the empty beginning, identification records of small states, witnesses."""
    start = empty()
    first = first_changes()
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    both = DState.of(2, [(0, 1)], [(0, 1)])
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    rec_two = record_of(two, 0, 1)
    rec_between = record_of(between, 0, 1)
    rec_both = record_of(both, 0, 1)
    merged_between = perform(between, ident)
    three = DState.of(3, [(0, 1), (0, 2)], [])
    rec_three = record_of(three, 0, 1)
    doc: dict[str, object] = {
        "state": written(start),
        "size": start.size,
        "changes": [c.written(start) for c in first],
        "two_term_empty_record": rec_two.as_json(),
        "two_term_empty_record_empty": rec_two.is_empty(),
        "two_term_empty_restored": restores_listed(two, ident),
        "two_term_between_record": rec_between.as_json(),
        "two_term_between_r_loop": list(rec_between.r.loop),
        "two_term_between_s_empty": rec_between.s.is_empty(),
        "r_record_not_s": rec_between.r != rec_between.s,
        "two_term_between_restored": restores_listed(between, ident),
        "two_term_both_records_agree": rec_both.r == rec_both.s,
        "r_determined_by_r": record_determined_by_rel(between, "r", 0, 1),
        "s_determined_by_s": record_determined_by_rel(between, "s", 0, 1),
        "identify_drops_a_term": merged_between.n == 1,
        "three_term_outgoing": [list(p) for p in rec_three.r.outgoing],
        "one_term_cost": cost(DState.of(1, [], [])),
        "reaches_itself_in_two_changes": cycle(start) is not None,
        "empty_changes": len(first),
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "r_record_not_s": bool(doc["r_record_not_s"]),
        "identify_drops_a_term": bool(doc["identify_drops_a_term"]),
        "empty_restored": bool(doc["two_term_empty_restored"]),
        "nonempty_not_restored": not bool(doc["two_term_between_restored"]),
    }


def write_records(out: Path, expl: Exploration, tag: str) -> dict[str, object]:
    """`records_<tag>.csv` and the record check of one exploration."""
    edges = check_records(expl)
    rows: list[list[object]] = []
    for state, change, outcome in performed(expl):
        if change.kind is not Kind.IDENTIFY:
            continue
        rec = record_of(state, change.x, change.y)
        rows.append(
            [
                state.key(),
                change.x,
                change.y,
                ",".join(rec.r.loop),
                ",".join(rec.s.loop),
                int(rec.r != rec.s),
                int(restores_listed(state, change)),
                expl.depth[state],
                outcome.key(),
            ]
        )
    _write_csv(
        out / f"records_{tag}.csv",
        ["state", "x", "y", "r_loop", "s_loop", "differs", "restored", "round", "outcome"],
        rows,
    )
    return records_summary(edges)


def records_summary(edges: RecordCheck) -> dict[str, object]:
    """The record check as a JSON object.  Disagreement lists empty on correct code."""
    return {
        "checked": edges.checked,
        "identifications": edges.identifications,
        "empty_records": edges.empty_records,
        "nonempty_records": edges.nonempty_records,
        "differs": edges.differs,
        "restored_empty": edges.restored_empty,
        "r_not_s": edges.r_not_s,
        "not_determined_by_rel": list(edges.not_determined_by_rel),
        "nonempty_restored": list(edges.nonempty_restored),
        "empty_not_restored_isolated": list(edges.empty_not_restored_isolated),
        "swap_mismatch": list(edges.swap_mismatch),
        "split_agrees": not (
            edges.not_determined_by_rel
            or edges.nonempty_restored
            or edges.empty_not_restored_isolated
            or edges.swap_mismatch
        ),
    }


def records_ok(block: dict[str, object]) -> bool:
    """The record classification of one run has no disagreement."""
    checked = block["checked"]
    assert isinstance(checked, int)
    if checked == 0:
        return True
    return bool(
        block["split_agrees"]
        and not block["not_determined_by_rel"]
        and not block["nonempty_restored"]
        and not block["empty_not_restored_isolated"]
        and not block["swap_mismatch"]
    )


def write_run(out: Path, bound: int, rounds: int, plan: Plan, keep_log: bool = False) -> dict[str, object]:
    """One C-M1 exploration: record classification and the ninth comparison."""
    del plan
    tag = run_tag(bound, rounds)
    expl = explore(empty(), bound, rounds, keep_log=keep_log)
    ninth = compare_with_ninth(expl)
    records = write_records(out, expl, tag)
    follows = record_verdicts(expl)
    state_verdicts = verdicts(expl)
    holding = [v.statement for v in state_verdicts if v.follows_within_bound]
    record_holding = [v.name for v in follows if v.follows]
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
        "records": records,
        "statements_holding_in_every_result": holding,
        "record_statements_holding_of_every_identification": record_holding,
        "two_term_rounds_equal_closed_form": two_term_ok,
        "results_that_reach_what_is_given": sum(1 for s in expl.depth if s.n == 0),
        "results_reached_from_what_is_given": len(expl.depth),
    }
    _write_json(out / f"summary_{tag}.json", row)
    if keep_log:
        recs = [
            {
                "state": state.key(),
                "change": change.written(state),
                "kind": change.kind.value,
                "outcome": outcome.key(),
                "record": None if change.kind is not Kind.IDENTIFY else record_of(state, change.x, change.y).as_json(),
                "performed": True,
            }
            for state, change, outcome in performed(expl)
        ]
        (out / f"attempts_{tag}.jsonl").write_text(
            "".join(json.dumps(r, sort_keys=True, ensure_ascii=True) + "\n" for r in recs),
            encoding="utf-8",
            newline="\n",
        )
    return row


def write_recorded(out: Path, bound: int, rounds: int) -> dict[str, object]:
    """The unchosen reading C-M2: recorded results, more than the ninth."""
    expl = explore_recorded(bound, rounds)
    ninth = explore_ninth(empty(), bound, rounds)
    one = DState.of(1, [], [])
    plain = Recorded(one, None)
    ident_rec = record_of(DState.of(2, [], []), 0, 1)
    tagged = Recorded(one, ident_rec)
    extra = len(expl.depth) - len(ninth.depth)
    size_failures = []
    for recorded, depth in expl.depth.items():
        if depth != recorded.size:
            size_failures.append(
                {
                    "state": recorded.state.key(),
                    "has_record": recorded.record is not None,
                    "recorded_cost": depth,
                    "size": recorded.size,
                }
            )
    doc: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "recorded_results": len(expl.depth),
        "ninth_results": len(ninth.depth),
        "extra_results": extra,
        "more_results_than_the_ninth": extra > 0,
        "one_term_plain_cost": recorded_cost(expl, plain),
        "one_term_identified_cost": recorded_cost(expl, tagged),
        "one_term_size": one.size,
        "recorded_cost_equals_size": not size_failures,
        "recorded_cost_failures": size_failures[:12],
        "recorded_cost_failure_count": len(size_failures),
        "plain_and_identified_are_two_results": plain != tagged,
        "beginning": {"state": recorded_start().state.key(), "record": None, "cost": 0},
    }
    _write_json(out / "recorded.json", doc)
    return doc


def recorded_ok(block: dict[str, object]) -> bool:
    """C-M2 has extra results; cost of a recorded identification is not always the size."""
    plain = block["one_term_plain_cost"]
    ident = block["one_term_identified_cost"]
    count = block["recorded_cost_failure_count"]
    assert isinstance(count, int)
    return bool(
        block["more_results_than_the_ninth"]
        and block["plain_and_identified_are_two_results"]
        and plain == block["one_term_size"] == 1
        and ident is not None
        and ident != 1
        and count >= 1
    )


def write_all(out: Path, plan: Plan | None = None) -> dict[str, object]:
    """Every computed file of `evidence/twelfth/`."""
    plan = plan or Plan()
    out.mkdir(parents=True, exist_ok=True)
    given = write_given(out)
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan, keep_log=False)
    log = write_run(out, plan.log_bound, plan.log_rounds, plan, keep_log=True)
    runs[run_tag(plan.log_bound, plan.log_rounds) + "_log"] = log
    recorded = write_recorded(out, plan.recorded_bound, plan.recorded_rounds)
    summary = {
        "plan": {
            "bound": plan.bound,
            "rounds": plan.rounds,
            "deep_bound": plan.deep_bound,
            "deep_rounds": plan.deep_rounds,
            "two_term_rounds": plan.two_term_rounds,
            "log_bound": plan.log_bound,
            "log_rounds": plan.log_rounds,
            "recorded_bound": plan.recorded_bound,
            "recorded_rounds": plan.recorded_rounds,
        },
        "given": given,
        "runs": runs,
        "recorded": recorded,
        "reading": "C-M1 record on the identification; C-M2 record in the result, unchosen, kept",
    }
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
