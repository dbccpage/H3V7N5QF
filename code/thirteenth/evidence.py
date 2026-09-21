"""Writes `evidence/thirteenth/`: every file is a pure function of the code, so it is regenerable.

Run `python code/generate_thirteenth.py` from the repository root.  No file holds
a date, a duration, or a machine name.

Cited from the first derivation (`xry.evidence`) and re-checked
    The CSV and JSON writers, the manifest and `compare_evidence` do not
    depend on the coarser writing.

Cited from the ninth derivation (`ninth.explore`, `ninth.orbits`, `ninth.cost`,
`ninth.reach`) and re-checked by computation
    The thirteenth exploration under C-C1 is the ninth's: the results, rounds
    and shortest-sequence counts must agree at the same bound.  Completeness
    within the bound is the ninth's independent count.  Coarser writings are
    filled on every result.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ninth.changes import Change, Kind, first_changes, perform
from ninth.explore import explore as explore_ninth
from ninth.orbits import count_results, two_term_round_count
from ninth.state import DState, empty, swap, written  # swap used in write_coarses / write_given
from seventh.orbits import counts_within as seventh_counts_within
from xry.evidence import _write_csv, _write_json, compare_evidence, write_manifest

from thirteenth.coarse import (
    add_r_or_s_same_coarser,
    coarse,
    coarse_key,
    determines,
    same_coarser,
    splits,
)
from thirteenth.cost import cost, coarse_cost
from thirteenth.explore import (
    Exploration,
    count_shortest_sequences,
    count_shortest_sequences_ninth,
    cycle,
    explore,
    explore_coarse,
    order,
    performed,
)
from thirteenth.follows import coarse_verdicts, verdicts
from thirteenth.invariants import CoarseCheck, check_coarses

__all__ = [
    "Plan",
    "coarse_ok",
    "coarses_ok",
    "compare_evidence",
    "compare_with_ninth",
    "count_shortest_sequences",
    "ninth_ok",
    "run_tag",
    "write_all",
    "write_coarse",
    "write_coarses",
    "write_given",
    "write_run",
]


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run.

    Under C-C1 the results of round `r` are the ninth's, so the bound is on
    terms and on rounds together as there.  The unchosen coarser reading is
    explored at `coarse_bound` terms and `coarse_rounds` rounds.
    """

    bound: int = 3
    rounds: int = 6
    deep_bound: int = 3
    deep_rounds: int = 5
    two_term_rounds: int = 8
    log_bound: int = 2
    log_rounds: int = 3
    coarse_bound: int = 2
    coarse_rounds: int = 5
    layers_upto: int = 8
    count_upto: int = 3
    count_total_upto: int = 6

    def runs(self) -> tuple[tuple[int, int], ...]:
        """The (terms, rounds) bounds of the C-C1 explorations written."""
        return ((self.bound, self.rounds), (self.deep_bound, self.deep_rounds), (2, self.two_term_rounds))


def run_tag(bound: int, rounds: int) -> str:
    """The file-name tag of one exploration."""
    return f"bound{bound}_rounds{rounds}"


def compare_with_ninth(expl: Exploration) -> dict[str, object]:
    """The thirteenth's results against the ninth's at the same bound and rounds."""
    ninth = explore_ninth(expl.start, expl.bound, expl.rounds)
    thirteenth_keys = set(expl.depth)
    ninth_keys = set(ninth.depth)
    extra = sorted((s.key() for s in thirteenth_keys - ninth_keys), key=str)
    missing = sorted((s.key() for s in ninth_keys - thirteenth_keys), key=str)
    round_disagreements = [
        s.key() for s in sorted(thirteenth_keys & ninth_keys, key=order) if expl.depth[s] != ninth.depth[s]
    ]
    sequences = count_shortest_sequences(expl)
    ninth_seq = count_shortest_sequences_ninth(ninth)
    seq_disagreements = [
        s.key() for s in sorted(thirteenth_keys & ninth_keys, key=order) if sequences.get(s) != ninth_seq.get(s)
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
        "thirteenth_results": len(expl.depth),
        "same_results": thirteenth_keys == ninth_keys,
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
    """`given.json`: the empty beginning, coarser writings of small states, witnesses."""
    start = empty()
    first = first_changes()
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    swapped = swap(between)
    both = DState.of(2, [(0, 1)], [(0, 1)])
    one = DState.of(1, [], [])
    added_r = perform(two, Change(Kind.ADD_ASSERTION, "r", 0, 1))
    added_s = perform(two, Change(Kind.ADD_ASSERTION, "s", 0, 1))
    doc: dict[str, object] = {
        "state": written(start),
        "size": start.size,
        "changes": [c.written(start) for c in first],
        "empty_determines": determines(start),
        "one_term_determines": determines(one),
        "two_term_empty_determines": determines(two),
        "two_term_between_determines": determines(between),
        "two_term_between_splits": splits(between),
        "r_and_s_same_coarser": same_coarser(between, swapped),
        "r_and_s_same_finer": between == swapped,
        "coarse_of_between": coarse(between).key(),
        "coarse_of_swapped": coarse(swapped).key(),
        "coarse_key_between": coarse_key(between),
        "add_r_or_s_same_coarser": add_r_or_s_same_coarser(two, 0, 1),
        "added_r_key": added_r.key(),
        "added_s_key": added_s.key(),
        "both_relations_splits": splits(both),
        "size_descends_between": coarse(between).size == between.size,
        "size_descends_empty": coarse(start).size == start.size,
        "one_term_cost": cost(one),
        "reaches_itself_in_two_changes": cycle(start) is not None,
        "empty_changes": len(first),
        "swap_keeps_coarse_both": coarse(swap(both)) == coarse(both),
    }
    _write_json(out / "given.json", doc)
    return {
        "changes_on_the_empty_state": len(first),
        "r_and_s_same_coarser": bool(doc["r_and_s_same_coarser"]),
        "r_and_s_differ_finer": not bool(doc["r_and_s_same_finer"]),
        "empty_determines": bool(doc["empty_determines"]),
        "between_not_determines": not bool(doc["two_term_between_determines"]),
        "add_r_or_s_same_coarser": bool(doc["add_r_or_s_same_coarser"]),
        "size_descends": bool(doc["size_descends_between"]),
    }


def write_coarses(out: Path, expl: Exploration, tag: str) -> dict[str, object]:
    """`coarses_<tag>.csv` and the coarser check of one exploration."""
    edges = check_coarses(expl)
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], s.n, s.key())):
        rows.append(
            [
                state.key(),
                coarse_key(state),
                int(determines(state)),
                splits(state),
                int(same_coarser(state, swap(state))),
                expl.depth[state],
                coarse(state).size,
                state.size,
            ]
        )
    _write_csv(
        out / f"coarses_{tag}.csv",
        ["state", "coarse", "determines", "splits", "swap_same_coarse", "round", "coarse_size", "size"],
        rows,
    )
    return coarses_summary(edges)


def coarses_summary(edges: CoarseCheck) -> dict[str, object]:
    """The coarser check as a JSON object.  Disagreement lists empty on correct code."""
    return {
        "checked": edges.checked,
        "determines_count": edges.determines_count,
        "not_determines_count": edges.not_determines_count,
        "swap_collapses": edges.swap_collapses,
        "add_r_s_same": edges.add_r_s_same,
        "not_sum": list(edges.not_sum),
        "not_size": list(edges.not_size),
        "not_swap": list(edges.not_swap),
        "determines_when_asserted": list(edges.determines_when_asserted),
        "not_determines_when_empty": list(edges.not_determines_when_empty),
        "splits_mismatch": list(edges.splits_mismatch),
        "add_r_s_fail": list(edges.add_r_s_fail),
        "split_agrees": not (
            edges.not_sum
            or edges.not_size
            or edges.not_swap
            or edges.determines_when_asserted
            or edges.not_determines_when_empty
            or edges.splits_mismatch
            or edges.add_r_s_fail
        ),
    }


def coarses_ok(block: dict[str, object]) -> bool:
    """The coarser classification of one run has no disagreement."""
    checked = block["checked"]
    assert isinstance(checked, int)
    if checked == 0:
        return True
    return bool(
        block["split_agrees"]
        and not block["not_sum"]
        and not block["not_size"]
        and not block["not_swap"]
        and not block["determines_when_asserted"]
        and not block["not_determines_when_empty"]
        and not block["splits_mismatch"]
        and not block["add_r_s_fail"]
    )


def write_run(out: Path, bound: int, rounds: int, plan: Plan, keep_log: bool = False) -> dict[str, object]:
    """One C-C1 exploration: coarser classification and the ninth comparison."""
    del plan
    tag = run_tag(bound, rounds)
    expl = explore(empty(), bound, rounds, keep_log=keep_log)
    ninth = compare_with_ninth(expl)
    coarses = write_coarses(out, expl, tag)
    follows = coarse_verdicts(expl)
    state_verdicts = verdicts(expl)
    holding = [v.statement for v in state_verdicts if v.follows_within_bound]
    coarse_holding = [v.name for v in follows if v.follows]
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
        "coarses": coarses,
        "statements_holding_in_every_result": holding,
        "coarse_statements_holding_of_every_result": coarse_holding,
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
                "coarse": coarse_key(outcome),
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


def write_coarse(out: Path, bound: int, rounds: int) -> dict[str, object]:
    """The unchosen reading C-C2: coarser results, fewer than the ninth."""
    expl = explore_coarse(bound, rounds)
    ninth = explore_ninth(empty(), bound, rounds)
    between = DState.of(2, [(0, 1)], [])
    swapped = swap(between)
    one = DState.of(1, [], [])
    one_coarse = coarse(one)
    extra = len(expl.depth) - len(ninth.depth)
    size_failures = []
    for written_state, depth in expl.depth.items():
        if depth != written_state.size:
            size_failures.append(
                {
                    "coarse": written_state.key(),
                    "coarse_cost": depth,
                    "size": written_state.size,
                }
            )
    seventh = seventh_counts_within(bound, rounds)
    seventh_total = sum(seventh.values())
    doc: dict[str, object] = {
        "bound_on_terms": bound,
        "rounds": rounds,
        "coarse_results": len(expl.depth),
        "ninth_results": len(ninth.depth),
        "extra_results": extra,
        "fewer_results_than_the_ninth": extra < 0,
        "seventh_independent_count": seventh_total,
        "explored_equals_seventh_count": len(expl.depth) == seventh_total,
        "one_term_coarse_cost": coarse_cost(expl, one_coarse),
        "one_term_size": one.size,
        "coarse_cost_equals_size": not size_failures,
        "coarse_cost_failures": size_failures[:12],
        "coarse_cost_failure_count": len(size_failures),
        "between_and_swap_same_coarse": same_coarser(between, swapped),
        "between_and_swap_differ_finer": between != swapped,
        "beginning": {"state": empty().key(), "coarse": coarse(empty()).key(), "cost": 0},
    }
    _write_json(out / "coarse.json", doc)
    return doc


def coarse_ok(block: dict[str, object]) -> bool:
    """C-C2 has fewer results; cost of a coarser result is the size; two finer collapse."""
    one_cost = block["one_term_coarse_cost"]
    count = block["coarse_cost_failure_count"]
    extra = block["extra_results"]
    assert isinstance(count, int) and isinstance(extra, int)
    return bool(
        block["fewer_results_than_the_ninth"]
        and extra < 0
        and block["between_and_swap_same_coarse"]
        and block["between_and_swap_differ_finer"]
        and one_cost == block["one_term_size"] == 1
        and count == 0
        and block["coarse_cost_equals_size"]
        and block["explored_equals_seventh_count"]
    )


def write_all(out: Path, plan: Plan | None = None) -> dict[str, object]:
    """Every computed file of `evidence/thirteenth/`."""
    plan = plan or Plan()
    out.mkdir(parents=True, exist_ok=True)
    given = write_given(out)
    runs: dict[str, object] = {}
    for bound, rounds in plan.runs():
        runs[run_tag(bound, rounds)] = write_run(out, bound, rounds, plan, keep_log=False)
    log = write_run(out, plan.log_bound, plan.log_rounds, plan, keep_log=True)
    runs[run_tag(plan.log_bound, plan.log_rounds) + "_log"] = log
    coarse_block = write_coarse(out, plan.coarse_bound, plan.coarse_rounds)
    summary = {
        "plan": {
            "bound": plan.bound,
            "rounds": plan.rounds,
            "deep_bound": plan.deep_bound,
            "deep_rounds": plan.deep_rounds,
            "two_term_rounds": plan.two_term_rounds,
            "log_bound": plan.log_bound,
            "log_rounds": plan.log_rounds,
            "coarse_bound": plan.coarse_bound,
            "coarse_rounds": plan.coarse_rounds,
        },
        "given": given,
        "runs": runs,
        "coarse": coarse_block,
        "reading": "C-C1 coarser writing on the result; C-C2 coarser writing is the result, unchosen, kept",
    }
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
