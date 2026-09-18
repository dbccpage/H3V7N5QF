"""Writes `evidence/`: every file is a pure function of the code, so it is regenerable.

Run `python -m xry` from the repository root (with `code/` on the path).
No file holds a date, a duration, or a machine name.
"""

from __future__ import annotations

import csv
import hashlib
import json
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from pathlib import Path

from xry.changes import Answer, Kind, changes, is_build_of, obstruction, one_term_builds
from xry.cost import cost, cost_free, cost_free_by_placement, destroyed
from xry.explore import Attempt, Exploration, check_answers, explore, order, rigid
from xry.follows import verdicts
from xry.orbits import NAMED_KINDS, count_named, count_one_way, count_states, layer_counts
from xry.state import Sameness, State, added, canonical, given


@dataclass(frozen=True)
class Plan:
    """The declared bounds of one evidence run."""

    free_bound: int = 5
    anchored_bound: int = 4
    log_bound: int = 3
    rounds: int = 100
    layers_upto: int = 20
    count_upto: int = 6

    def bound(self, sameness: Sameness) -> int:
        """The declared bound on the number of terms under `sameness`."""
        return self.free_bound if sameness is Sameness.FREE else self.anchored_bound


def alternative(bra: bool) -> str:
    """The name of an initial alternative in file names and tables."""
    return "with_bra" if bra else "without_bra"


def _write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def _write_json(path: Path, value: object) -> None:
    text = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True)
    path.write_text(text + "\n", encoding="utf-8", newline="\n")


def states_on_given_terms() -> tuple[State, ...]:
    """Every legal state on the terms `a`, `b` alone in which `arb` is asserted."""
    out = []
    for mask in range(16):
        state = State(2, mask, (0, 1))
        if state.legal and state.has(0, 1):
            out.append(state)
    return tuple(out)


def _further_written(state: State, ans: Answer) -> list[str]:
    """The further changes of an answer, in words.

    A change that mentions an added term is written with the writing of the
    answer's result (which has that term); the others with the state's.
    """
    return [
        c.written(ans.result if max(c.x, c.y) >= state.n else state) for c in ans.further
    ]


def attempt_record(rec: Attempt, round_: int) -> dict[str, object]:
    """One attempt as the seed asks: the change, the obstruction, the answer."""
    w = rec.state.term_writing()
    return {
        "state": rec.state.key(),
        "written": rec.state.written(),
        "round": round_,
        "change": rec.change.written(rec.state),
        "adds": list(rec.change.additions),
        "obstruction": [f"{w[x]}r{w[y]}" for x, y in rec.obstruction],
        "outcome": None if rec.outcome is None else rec.outcome.key(),
        "beyond_bound": rec.beyond,
        "answers": [
            {
                "answer": ans.kind.value,
                "further": _further_written(rec.state, ans),
                "completes_the_change": ans.completes,
                "changes_performed": ans.performed,
                "result": canonical(ans.result).key(),
            }
            for ans in rec.answers
        ],
    }


def write_given(out: Path) -> dict[str, object]:
    """`given.json`: the alternatives for what is given, and every attempt on them."""
    found = states_on_given_terms()
    doc: dict[str, object] = {
        "legal_states_on_the_given_terms_with_arb": [s.written() for s in found],
        "count": len(found),
    }
    not_builds = 0
    for sameness in Sameness:
        for bra in (False, True):
            start = given(bra, sameness)
            expl = explore(start, bound=3, rounds=1, keep_log=True)
            builds = {}
            for change in changes(start):
                if change.kind is Kind.ADD_ASSERTION and obstruction(start, change):
                    all_builds = one_term_builds(start, change.x)
                    not_builds += sum(1 for b in all_builds if not is_build_of(b, start, change))
                    distinct = sorted({canonical(b) for b in all_builds}, key=order)
                    builds[change.written(start)] = {
                        "one_term_builds": len(all_builds),
                        "up_to_sameness": [b.written() for b in distinct],
                    }
            doc[f"{sameness.value}/{alternative(bra)}"] = {
                "state": start.written(),
                "attempts": [attempt_record(rec, 1) for rec in expl.log],
                "builds_with_one_added_term": builds,
            }
    one = State.of(1, [])
    on_one = one_term_builds(one, 0)
    doc["builds_answering_xrx_on_one_term"] = {
        "state": one.written(),
        "one_term_builds": [b.written() for b in on_one],
        "up_to_free_sameness": [
            b.written() for b in sorted({canonical(b) for b in on_one}, key=order)
        ],
        "these_are_the_alternatives_for_what_is_given": {canonical(b) for b in on_one}
        == {canonical(given(bra, Sameness.FREE)) for bra in (False, True)},
    }
    _write_json(out / "given.json", doc)
    return {"states_on_given_terms": len(found), "listed_builds_that_are_not_builds": not_builds}


def result_rows(expl: Exploration, bra: bool) -> list[list[object]]:
    """One row per result: what it adds to what is given, when it appears, its cost."""
    rows: list[list[object]] = []
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        terms, assertions = added(state)
        tried = changes(state)
        blocked = [c for c in tried if obstruction(state, c)]
        rows.append(
            [
                state.key(),
                state.written(),
                state.n,
                state.m,
                terms,
                assertions,
                expl.depth[state],
                cost(state, bra),
                "" if state.names is None else destroyed(state, bra),
                len(tried),
                sum(1 for c in blocked if c.kind is Kind.IDENTIFY),
                sum(1 for c in blocked if c.kind is Kind.ADD_ASSERTION),
                int(rigid(state)),
            ]
        )
    return rows


RESULT_HEADER = (
    "state",
    "written",
    "terms",
    "assertions",
    "terms_added_to_given",
    "assertions_added_to_given",
    "round_first_reached",
    "fewest_changes_by_formula",
    "destroyed_givens",
    "changes_attempted",
    "obstructed_identifications",
    "obstructed_additions",
    "every_identification_obstructed",
)


def added_rows(expl: Exploration) -> list[list[int]]:
    """Results grouped by (terms added, assertions added), fewest additions first."""
    groups: dict[tuple[int, int], list[int]] = {}
    for state, round_ in expl.depth.items():
        groups.setdefault(added(state), []).append(round_)
    ordered = sorted(groups, key=lambda k: (max(k[0], 0) + max(k[1], 0), k))
    return [[t, a, len(groups[t, a]), min(groups[t, a]), max(groups[t, a])] for t, a in ordered]


def frontier_rows(expl: Exploration) -> list[list[object]]:
    """One row per frontier state, with how many of its attempts leave the bound."""
    per_state: dict[State, dict[str, int]] = {}
    for leave in expl.frontier:
        ways = per_state.setdefault(leave.state, {})
        ways[leave.by] = ways.get(leave.by, 0) + 1
    return [
        [
            state.key(),
            state.written(),
            expl.depth[state],
            per_state[state].get("the change", 0),
            per_state[state].get("build structure", 0),
        ]
        for state in sorted(per_state, key=order)
    ]


def write_run(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> dict[str, object]:
    """All files of one exploration; returns its summary."""
    tag = f"{sameness.value}_{alternative(bra)}"
    bound = plan.bound(sameness)
    expl = explore(given(bra, sameness), bound, plan.rounds)

    _write_csv(out / f"results_{tag}.csv", RESULT_HEADER, result_rows(expl, bra))
    _write_csv(
        out / f"added_{tag}.csv",
        ("terms_added_to_given", "assertions_added_to_given", "results", "first_round", "last_round"),
        added_rows(expl),
    )
    _write_csv(
        out / f"frontier_{tag}.csv",
        ("state", "written", "round_first_reached", "leaves_by_the_change", "leaves_by_a_build"),
        frontier_rows(expl),
    )

    exact = layer_counts(sameness, bra, plan.layers_upto)
    so_far = 0
    round_rows: list[list[object]] = []
    for r in range(plan.rounds + 1):
        so_far += expl.new_per_round[r]
        round_rows.append(
            [
                r,
                expl.new_per_round[r],
                so_far,
                expl.attempts_per_round[r],
                expl.obstructed_per_round[r],
                exact[r] if r < len(exact) else "",
            ]
        )
    _write_csv(
        out / f"rounds_{tag}.csv",
        (
            "round",
            "new_results_within_bound",
            "results_so_far_within_bound",
            "changes_attempted_so_far",
            "of_which_obstructed",
            "new_results_without_bound_by_formula",
        ),
        round_rows,
    )

    found = verdicts(expl)
    _write_csv(
        out / f"follows_{tag}.csv",
        ("statement", "wording", "in_what_is_given", "first_holds", "round", "first_fails", "round_"),
        [
            [
                v.statement,
                v.wording,
                int(v.in_given),
                "" if v.holds_at is None else v.holds_at.written(),
                "" if v.holds_round is None else v.holds_round,
                "" if v.fails_at is None else v.fails_at.written(),
                "" if v.fails_round is None else v.fails_round,
            ]
            for v in found
        ],
    )

    by_terms: dict[int, dict[int, int]] = {}
    for state in expl.depth:
        by_m = by_terms.setdefault(state.n, {})
        by_m[state.m] = by_m.get(state.m, 0) + 1
    counted = {
        n: {m: c for m, c in enumerate(count_states(sameness, n)) if c}
        for n in range(1, bound + 1)
    }
    mismatches = [s.key() for s, r in expl.depth.items() if cost(s, bra) != r]
    # Rounds 0 .. N - 2 are complete within the bound; only rounds that were run can be compared.
    within_bound_layers = min(plan.layers_upto, bound - 2, plan.rounds)
    check = check_answers(expl)
    entries: dict[State, int] = {}
    for leave in expl.frontier:
        entries[leave.state] = entries.get(leave.state, 0) + 1
    full = {s for s in expl.depth if s.n == bound}
    one_plus_two_n = set(entries) == full and all(c == 1 + 2 * s.n for s, c in entries.items())
    return {
        "bound_on_terms": bound,
        "rounds": plan.rounds,
        "results": len(expl.depth),
        "results_by_terms": {str(n): sum(by_terms[n].values()) for n in sorted(by_terms)},
        "last_round_with_a_new_result": expl.last_new_round,
        "explored_equals_independent_count": by_terms == counted,
        "round_equals_cost_formula_for_every_result": not mismatches,
        "cost_formula_mismatches": mismatches,
        "rounds_agreeing_with_unbounded_formula": [
            expl.new_per_round[r] == exact[r] for r in range(within_bound_layers + 1)
        ],
        "frontier_states": len(entries),
        "frontier_attempts": len({(leave.state, leave.change) for leave in expl.frontier}),
        "frontier_entries": len(expl.frontier),
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": one_plus_two_n,
        "obstructed_attempts": check.obstructed,
        "answers_within_bound": check.answers_within,
        "answers_beyond_bound": check.answers_beyond,
        "answers_reaching_something_new": list(check.failures),
        "every_identification_obstructed": sum(1 for s in expl.depth if rigid(s)),
        "statements_holding_in_every_result": [v.statement for v in found if v.follows_within_bound],
        "statements_that_do_not_follow": [v.statement for v in found if v.independent],
    }


def write_log(out: Path, sameness: Sameness, bra: bool, plan: Plan) -> int:
    """The full attempt log of a small exploration (bound `plan.log_bound`)."""
    expl = explore(given(bra, sameness), plan.log_bound, plan.rounds, keep_log=True)
    path = out / f"attempts_bound{plan.log_bound}_{sameness.value}_{alternative(bra)}.jsonl"
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for rec in expl.log:
            line = attempt_record(rec, expl.depth[rec.state] + 1)
            handle.write(json.dumps(line, sort_keys=True, ensure_ascii=True) + "\n")
    return len(expl.log)


def write_counts(out: Path, plan: Plan) -> dict[str, list[int]]:
    """`counts.csv`: legal states by terms and assertions, by independent count."""
    rows: list[list[object]] = []
    totals: dict[str, list[int]] = {"free": [], "free_one_way": [], "anchored": []}
    for n in range(1, plan.count_upto + 1):
        free = count_states(Sameness.FREE, n)
        one_way = count_one_way(n)
        named = count_named(n)
        totals["free"].append(sum(free))
        totals["free_one_way"].append(sum(one_way))
        totals["anchored"].append(sum(sum(v) for v in named.values()))
        for m, count in enumerate(free):
            rows.append([n, m, count, one_way[m], *(named[kind][m] for kind in NAMED_KINDS)])
    _write_csv(
        out / "counts.csv",
        ("terms", "assertions", "free", "free_never_both_ways", *(f"anchored: {k}" for k in NAMED_KINDS)),
        rows,
    )
    return totals


def check_free_cost(bound: int) -> tuple[int, list[str]]:
    """Compare the closed form for FREE cost with the best placement of names.

    Returns how many (state, alternative) pairs were compared, and the keys of
    those where the two disagree.
    """
    checked = 0
    mismatches = []
    for bra in (False, True):
        expl = explore(given(bra, Sameness.FREE), bound, rounds=bound * bound + 4)
        for state in expl.depth:
            if cost_free(state, bra) != cost_free_by_placement(state, bra):
                mismatches.append(f"{alternative(bra)}/{state.key()}")
            checked += 1
    return checked, mismatches


def compare_evidence(committed: Path, fresh: Path) -> list[str]:
    """How a committed evidence folder differs from a fresh regeneration of it.

    `lean_axioms.txt` is written by `xry.leanreport`, not by this module, so it
    and its manifest line are left out of the comparison.
    """
    skip = {"MANIFEST.sha256", "lean_axioms.txt"}
    names_a = {p.name for p in committed.iterdir() if p.is_file()} - skip
    names_b = {p.name for p in fresh.iterdir() if p.is_file()} - skip
    out = [f"only in {committed}: {n}" for n in sorted(names_a - names_b)]
    out += [f"only in the regeneration: {n}" for n in sorted(names_b - names_a)]
    for name in sorted(names_a & names_b):
        if (committed / name).read_bytes() != (fresh / name).read_bytes():
            out.append(f"differs: {name}")

    def manifest(folder: Path) -> list[str]:
        path = folder / "MANIFEST.sha256"
        if not path.is_file():
            return []
        lines = path.read_text(encoding="utf-8").splitlines()
        return [line for line in lines if not line.endswith("  lean_axioms.txt")]

    if manifest(committed) != manifest(fresh):
        out.append("differs: MANIFEST.sha256 (lean_axioms.txt line left out)")
    return out


def write_manifest(out: Path) -> int:
    """`MANIFEST.sha256`: a hash for every other file in `out`."""
    lines = []
    for path in sorted(out.iterdir(), key=lambda p: p.name):
        if path.is_file() and path.name != "MANIFEST.sha256":
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            lines.append(f"{digest}  {path.name}\n")
    (out / "MANIFEST.sha256").write_text("".join(lines), encoding="utf-8", newline="\n")
    return len(lines)


def write_all(out: Path, plan: Plan) -> dict[str, object]:
    """Write every computed evidence file into `out`; return the summary."""
    out.mkdir(parents=True, exist_ok=True)
    checked, cost_mismatches = check_free_cost(min(plan.free_bound, 4))
    summary: dict[str, object] = {
        "plan": {
            "bound_on_terms_free": plan.free_bound,
            "bound_on_terms_anchored": plan.anchored_bound,
            "bound_on_terms_full_log": plan.log_bound,
            "rounds": plan.rounds,
            "unbounded_round_counts_upto": plan.layers_upto,
        },
        "given": write_given(out),
        "independent_counts": write_counts(out, plan),
        "free_cost_closed_form_checked_on": checked,
        "free_cost_closed_form_mismatches": cost_mismatches,
    }
    runs: dict[str, object] = {}
    logged: dict[str, int] = {}
    for sameness in Sameness:
        for bra in (False, True):
            tag = f"{sameness.value}/{alternative(bra)}"
            runs[tag] = write_run(out, sameness, bra, plan)
            logged[tag] = write_log(out, sameness, bra, plan)
    summary["runs"] = runs
    summary["attempts_in_full_logs"] = logged
    _write_json(out / "summary.json", summary)
    write_manifest(out)
    return summary
