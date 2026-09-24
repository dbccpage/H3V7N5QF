"""Writes `evidence/fifteenth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_fifteenth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on admission.

Cited from the ninth derivation (`ninth.explore`, `ninth.orbits`, `ninth.cost`,
`ninth.reach`) and re-checked by computation
    The fifteenth exploration under C-A1 is the ninth's: the results, rounds
    and shortest-sequence counts must agree at the same bound.  Completeness
    within the bound is the ninth's independent count.  Admission is filled
    on every reached result as not-admitted.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ninth.changes import first_changes
from ninth.explore import explore as explore_ninth
from ninth.orbits import count_results, two_term_round_count
from ninth.state import DState, empty, written
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from fifteenth.admission import admitted_record, admission_of_reaching, can_admit, not_admitted_record
from fifteenth.changes import admission_counts
from fifteenth.cost import cost, tagged_cost
from fifteenth.explore import (
    Exploration,
    attempt,
    count_shortest_sequences,
    count_shortest_sequences_ninth,
    cycle,
    explore,
    explore_tagged,
    admission_performed,
    order,
)
from fifteenth.follows import admission_verdicts, verdicts
from fifteenth.invariants import AdmissionCheck, check_admissions
from fifteenth.state import Tagged, tagged_start

__all__ = [
    "Plan",
    "compare_evidence",
    "compare_with_ninth",
    "count_shortest_sequences",
    "admission_of_reaching",
    "admissions_ok",
    "ninth_ok",
    "run_tag",
    "tagged_ok",
    "write_all",
    "write_given",
    "write_admissions",
    "write_run",
    "write_tagged",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Under C-A1 the results of round `r` are the ninth's, so the bound is on
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
        """The (terms, rounds) bounds of the C-A1 explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def compare_with_ninth(expl: Exploration) -> dict[str, object]:
    """The fifteenth's results against the ninth's at the same bound and rounds."""
    ninth = explore_ninth(expl.start, expl.bound, expl.rounds)
    fifteenth_keys = set(expl.depth)
    ninth_keys = set(ninth.depth)
    extra = sorted((s.key() for s in fifteenth_keys - ninth_keys), key=str)
    missing = sorted((s.key() for s in ninth_keys - fifteenth_keys), key=str)
    round_disagreements = [
        s.key() for s in sorted(fifteenth_keys & ninth_keys, key=order) if expl.depth[s] != ninth.depth[s]
    ]
    sequences = count_shortest_sequences(expl)
    ninth_seq = count_shortest_sequences_ninth(ninth)
    seq_disagreements = [
        s.key() for s in sorted(fifteenth_keys & ninth_keys, key=order) if sequences.get(s) != ninth_seq.get(s)
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
        "fifteenth_results": len(expl.depth),
        "same_results": fifteenth_keys == ninth_keys,
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
    """`given.json`: the empty beginning, admission of its one change, witnesses."""
    start = empty()
    first = first_changes()
    rec = attempt(start, first[0], bound=2)
    one = DState.of(1, [], [])
    r_only = DState.of(2, [(0, 1)], [])
    s_only = DState.of(2, [], [(0, 1)])
    both = DState.of(1, [(0, 0)], [(0, 0)])
    first_admission = admission_of_reaching(rec.outcome if rec.outcome is not None else start)
    r_admission = admission_of_reaching(r_only)
    s_admission = admission_of_reaching(s_only)
    both_admission = admission_of_reaching(both)
    doc: dict[str, object] = {
        "state": written(start),
        "size": start.size,
        "changes": [c.written(start) for c in first],
        "admission_of_the_first_outcome": first_admission.written(),
        "the_first_change_does_not_admit": not first_admission.admitted,
        "first_admission_is_assertion": first_admission.is_assertion(),
        "first_admission_is_change": first_admission.is_change(),
        "first_admission_is_xry": first_admission.is_xry(),
        "first_admission_is_xsy": first_admission.is_xsy(),
        "first_admission_of_r": first_admission.is_of_relation("r"),
        "outcome_of_the_first_change": None if rec.outcome is None else written(rec.outcome),
        "one_term_cost": cost(one),
        "one_term_admission": admission_of_reaching(one).written(),
        "r_only_admission": r_admission.written(),
        "s_only_admission": s_admission.written(),
        "r_and_s_same_admission": r_admission == s_admission,
        "both_admission": both_admission.written(),
        "can_admit_empty": can_admit(start),
        "can_admit_one": can_admit(one),
        "reaches_itself_in_two_changes": cycle(start) is not None,
        "empty_changes": len(first),
        "admitted_written_uses_neither_r_nor_s": admitted_record().written() == "admitted",
        "not_admitted_written": not_admitted_record().written() == "not-admitted",
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "admission_of_the_first_outcome": first_admission.written(),
        "r_and_s_same_admission": bool(doc["r_and_s_same_admission"]),
        "admission_not_assertion": not bool(doc["first_admission_is_assertion"]),
        "admission_not_a_kind": not bool(doc["first_admission_is_change"]),
        "reaching_does_not_admit": bool(doc["the_first_change_does_not_admit"]),
    }


def write_admissions(out: Path, expl: Exploration, tag: str) -> dict[str, object]:
    """`admissions_<tag>.csv` and the admission check of one exploration."""
    edges = check_admissions(expl)
    rows: list[list[object]] = []
    for state, change, arrived, record in admission_performed(expl):
        rows.append(
            [
                state.key(),
                change.written(state),
                change.kind.value,
                change.rel or "",
                record.written(),
                int(record.admitted),
                arrived.key(),
                int(record.is_assertion()),
            ]
        )
    _write_csv(
        out / f"admissions_{tag}.csv",
        ["state", "change", "kind", "relation", "admission", "admitted", "outcome", "is_assertion"],
        rows,
    )
    return admission_summary(edges)


def admission_summary(edges: AdmissionCheck) -> dict[str, object]:
    """The admission check as a JSON object.  Disagreement lists empty on correct code."""
    return {
        "checked": edges.checked,
        "not_admitted": edges.not_admitted,
        "admitted": edges.admitted,
        "reaching_never_admits": edges.admitted == 0 and edges.not_admitted == edges.checked,
        "reaching_admits": list(edges.reaching_admits),
        "cannot_admit": list(edges.cannot_admit),
        "assertion_records": list(edges.assertion_records),
        "kind_records": list(edges.kind_records),
        "of_relation": list(edges.of_relation),
        "cross_relation_disagree": list(edges.cross_relation_disagree),
        "split_agrees": not (
            edges.reaching_admits
            or edges.cannot_admit
            or edges.assertion_records
            or edges.kind_records
            or edges.of_relation
            or edges.cross_relation_disagree
        ),
    }


def admissions_ok(block: dict[str, object]) -> bool:
    """The admission classification of one run has no disagreement."""
    checked = block["checked"]
    assert isinstance(checked, int)
    if checked == 0:
        return True
    return bool(
        block["split_agrees"]
        and block["reaching_never_admits"]
        and not block["reaching_admits"]
        and not block["cannot_admit"]
        and not block["assertion_records"]
        and not block["kind_records"]
        and not block["of_relation"]
        and not block["cross_relation_disagree"]
    )


def write_run(out: Path, bound: int, rounds: int, plan: Plan, keep_log: bool = False) -> dict[str, object]:
    """One C-A1 exploration: admission classification and the ninth comparison."""
    del plan
    tag = run_tag(bound, rounds)
    expl = explore(empty(), bound, rounds, keep_log=keep_log)
    ninth = compare_with_ninth(expl)
    admissions = write_admissions(out, expl, tag)
    follows = admission_verdicts(expl)
    state_verdicts = verdicts(expl)
    holding = [v.statement for v in state_verdicts if v.follows_within_bound]
    admission_holding = [v.name for v in follows if v.follows]
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
    counts = admission_counts(empty())
    row: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "results": len(expl.depth),
        "results_with_a_term": sum(1 for s in expl.depth if s.n >= 1),
        "the_first_round_is_the_one_term_state_alone": (
            expl.new_per_round[1] == 1 if rounds >= 1 else None
        ),
        "empty_changes": counts[0],
        "empty_reaching_admits": counts[1],
        "empty_not_admitted": counts[2],
        "ninth_derivation": ninth,
        "admissions": admissions,
        "statements_holding_in_every_result": holding,
        "admission_statements_holding_of_every_result": admission_holding,
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
                    "admission": rec.admission.written(),
                    "admitted": rec.admission.admitted,
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
    """The unchosen reading C-A2: tagged results, cost not the size."""
    expl = explore_tagged(bound, rounds)
    ninth = explore_ninth(empty(), bound, rounds)
    one = DState.of(1, [], [])
    admitted_one = Tagged(one, admitted_record())
    nothing_one = Tagged(one, not_admitted_record())
    extra = len(expl.depth) - len(ninth.depth)
    size_failures = []
    for tagged, depth in expl.depth.items():
        if depth != tagged.size:
            size_failures.append(
                {
                    "state": tagged.state.key(),
                    "admission": tagged.admission.written(),
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
        "one_term_not_admitted_cost": tagged_cost(expl, nothing_one),
        "one_term_admitted_cost": tagged_cost(expl, admitted_one),
        "one_term_size": one.size,
        "tagged_cost_exceeds_size": bool(size_failures),
        "tagged_cost_failures": size_failures_head,
        "tagged_cost_failure_count": len(size_failures),
        "beginning": {
            "state": tagged_start().state.key(),
            "admission": tagged_start().admission.written(),
            "cost": 0,
        },
    }
    _write_json(out / "tagged.json", doc)
    return doc


def tagged_ok(block: dict[str, object]) -> bool:
    """C-A2 has extra results and a cost that is not the size."""
    admitted_cost = block["one_term_admitted_cost"]
    return bool(
        block["more_results_than_the_ninth"]
        and block["tagged_cost_exceeds_size"]
        and block["one_term_not_admitted_cost"] == block["one_term_size"] == 1
        and admitted_cost is not None
        and int(str(admitted_cost)) > 1
    )


def write_all(out: Path, plan: Plan | None = None) -> dict[str, object]:
    """Every computed file of `evidence/fifteenth/`."""
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
        "reading": "C-A1 admission recorded with the result, not in the state; C-A2 admission in the result, unchosen, kept",
    }
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
