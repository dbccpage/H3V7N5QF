"""Gate: every differential check must BITE when the derivation is mutated.

The dynamic OEWAS layer (see `ci/OEWAS_GATES.md`).  A differential check is a
*fitness assay* for a derivation: it should fail when the derivation computes
the wrong thing.  A check that cannot be made to fail by any perturbation is
under no selective pressure -- it is vacuous, however green it is.  This gate
applies mutation testing to the checks: for each disagreement field of each
derivation's check dataclass it runs the derivation on a small exploration
(the baseline must be clean), applies the mutation that should make that field
fire, and requires it to fire.  A field that does not fire under its mutation
-- because it compares a value with itself, or is dead -- fails the gate.

Completeness.  The panel enumerates every list-valued field of each `*Check`
dataclass and requires a registered bite case for each.  A new disagreement
field with no bite case fails the gate; a bite case for a field that no longer
exists fails too.  So no check can hide unregistered.

Soundness of the mutation.  A perturbation of a *record* function
(`leftover_of`, `admission_of_reaching`, `record_of`, `coarse`) is applied at
EVERY binding site (`patch_everywhere`): a `from x import f` copies the
reference, and a vacuous check comparing the record against a copy of itself
through two bindings would spuriously disagree if only one were patched.
Predicate mutations (`is_assertion`, `can_admit`, ...) are single-site: they
gate a guard field, not a differential comparison.

Injection-proven in `tests/test_mutation_bite.py`: the fifteenth's ORIGINAL
vacuous cross-relation check (a value compared with a copy of itself) survives
the mutation, and the gate reports it; and removing a bite case makes the
completeness check name the uncovered field.

Run: `python ci/check_mutation_bite.py` (exit 1 on an uncovered or non-biting
field).
"""

from __future__ import annotations

import argparse
import dataclasses
import sys
from collections.abc import Callable, Iterator
from contextlib import AbstractContextManager, contextmanager
from pathlib import Path
from typing import Any
from unittest.mock import patch

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "code"))

Mutation = Callable[[], "AbstractContextManager[None]"]  # a factory of context managers


def _nonempty_lists(record: Any) -> frozenset[str]:
    """Names of the list-valued fields of a check dataclass that are non-empty."""
    assert dataclasses.is_dataclass(record)
    return frozenset(
        f.name for f in dataclasses.fields(record) if isinstance(getattr(record, f.name), list) and getattr(record, f.name)
    )


def disagreement_fields(check_class: type) -> frozenset[str]:
    """The list-valued fields of a `*Check` dataclass -- its disagreement lists."""
    return frozenset(f.name for f in dataclasses.fields(check_class) if "list" in str(f.type))


@contextmanager
def everywhere(package: str, attr: str, replacement: Callable[..., Any]) -> Iterator[None]:
    """Replace `attr` on every loaded module of `package` that binds it (uniform perturbation)."""
    patches = [
        patch(f"{name}.{attr}", replacement)
        for name, module in list(sys.modules.items())
        if name.startswith(package + ".") and hasattr(module, attr)
    ]
    for p in patches:
        p.start()
    try:
        yield
    finally:
        for p in patches:
            p.stop()


@contextmanager
def _one(target: str, replacement: Any) -> Iterator[None]:
    with patch(target, replacement):
        yield


@contextmanager
def _both(a: tuple[str, Any], b: tuple[str, Any]) -> Iterator[None]:
    with patch(a[0], a[1]), patch(b[0], b[1]):
        yield


@dataclasses.dataclass
class Panel:
    """One derivation's check surface: how to run it, and a mutation per field."""

    derivation: str
    check_class: type
    signals: Callable[[], frozenset[str]]
    cases: dict[str, Mutation]


def check_panel(panel: Panel) -> list[str]:
    """Every failure of one panel: uncovered fields, stray cases, and non-biting fields."""
    problems: list[str] = []
    fields = disagreement_fields(panel.check_class)
    covered = set(panel.cases)
    for field in sorted(fields - covered):
        problems.append(f"{panel.derivation}: field `{field}` has no bite case (uncovered -- add one or remove the field)")
    for field in sorted(covered - fields):
        problems.append(f"{panel.derivation}: bite case `{field}` names no field of {panel.check_class.__name__}")
    baseline = panel.signals()
    for field, mutation in sorted(panel.cases.items()):
        if field not in fields:
            continue
        if field in baseline:
            problems.append(f"{panel.derivation}: `{field}` is non-empty at baseline -- not a clean bite test")
            continue
        with mutation():
            fired = panel.signals()
        if field not in fired:
            problems.append(f"{panel.derivation}: `{field}` does not fire under its mutation -- the check does not bite (vacuous)")
    return problems


# --- the antigen panels ---------------------------------------------------


def _fifteenth() -> Panel:
    from fifteenth.admission import Admission, admitted_record
    from fifteenth.explore import explore
    from fifteenth.invariants import AdmissionCheck, check_admissions
    from ninth.state import DState, empty

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_admissions(explore(empty(), 2, 4)))

    def relation_dependent() -> Any:
        def wrong(s: Any) -> Admission:
            return Admission(True) if isinstance(s, DState) and s.total_r > s.total_s else Admission(False)

        return everywhere("fifteenth", "admission_of_reaching", wrong)

    cases: dict[str, Mutation] = {
        "reaching_admits": lambda: _one("fifteenth.explore.admission_of_reaching", lambda _s: admitted_record()),
        "cannot_admit": lambda: _one("fifteenth.invariants.can_admit", lambda _s: False),
        "assertion_records": lambda: _one("fifteenth.admission.Admission.is_assertion", lambda self: True),
        "kind_records": lambda: _one("fifteenth.invariants.admission_is_a_kind", lambda _r: True),
        "of_relation": lambda: _one("fifteenth.admission.Admission.is_of_relation", lambda self, rel: True),
        "cross_relation_disagree": relation_dependent,
    }
    return Panel("fifteenth", AdmissionCheck, signals, cases)


def _fourteenth() -> Panel:
    from fourteenth.explore import explore
    from fourteenth.invariants import LeftoverCheck, check_leftovers
    from fourteenth.leftover import leftover_of as real, leftover_merge, leftover_nothing, leftover_pair
    from ninth.state import empty

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_leftovers(explore(empty(), 2, 4)))

    def relation_dependent() -> Any:
        def wrong(state: Any, change: Any) -> Any:
            return leftover_pair(9, 9) if change.rel == "s" else real(state, change)

        return everywhere("fourteenth", "leftover_of", wrong)

    cases: dict[str, Mutation] = {
        "additions_not_nothing": lambda: everywhere("fourteenth", "leftover_of", lambda _s, _c: leftover_merge(0, 1)),
        "removals_not_pair": lambda: everywhere("fourteenth", "leftover_of", lambda _s, _c: leftover_nothing()),
        "identify_not_merge": lambda: everywhere("fourteenth", "leftover_of", lambda _s, _c: leftover_nothing()),
        "assertion_writings": lambda: _one("fourteenth.leftover.LeftWriting.is_assertion", lambda self: True),
        "answer_writings": lambda: _one("fourteenth.leftover.LeftWriting.is_answer", lambda self: True),
        "clearing_kind": lambda: _one("fourteenth.invariants.clearing_is_a_kind", lambda _w: True),
        "cross_relation_disagree": relation_dependent,
    }
    return Panel("fourteenth", LeftoverCheck, signals, cases)


def _tenth() -> Panel:
    from ninth.changes import Kind
    from ninth.state import empty
    from tenth.explore import explore
    from tenth.invariants import LeftoverCheck, check_leftovers
    from tenth.leftover import LeftOver, leftover_of as real

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_leftovers(explore(empty(), 3, 5)))

    def flip_identify() -> Any:
        flip = {LeftOver.CLEARABLE: LeftOver.UNCLEARED, LeftOver.UNCLEARED: LeftOver.CLEARABLE}

        def wrong(state: Any, change: Any) -> Any:
            right = real(state, change)
            return flip.get(right, right) if change.kind is Kind.IDENTIFY else right

        return everywhere("tenth", "leftover_of", wrong)

    cases: dict[str, Mutation] = {
        "additions_not_nothing": lambda: everywhere("tenth", "leftover_of", lambda _s, _c: LeftOver.UNCLEARED),
        "removals_not_clearable": lambda: everywhere("tenth", "leftover_of", lambda _s, _c: LeftOver.NOTHING_LEFT),
        "other_relation_cleared": lambda: _one("tenth.invariants.other_clears", lambda _s, _c: True),
        "identify_disagreements": flip_identify,
        "clearing_failed": lambda: _one("tenth.invariants.clearing_change", lambda _c: None),
    }
    return Panel("tenth", LeftoverCheck, signals, cases)


def _eleventh() -> Panel:
    from eleventh.invariants import WritingCheck, check_writings
    from eleventh.explore import explore
    from ninth.state import DState, empty

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_writings(explore(empty(), 3, 3)))

    cases: dict[str, Mutation] = {
        "injective_not_determining": lambda: _one("eleventh.invariants.determines", lambda _s, _w: False),
        "coarser_of_collision_determines": lambda: _one("eleventh.invariants.coarser_than", lambda _a, _b: True),
        "identify_kept_both_terms": lambda: _one("eleventh.invariants.perform", lambda s, _c: s),
        "collide_dropped_a_term": lambda: _one("eleventh.invariants.terms_after_writing", lambda _s, _w: 0),
    }
    del DState
    return Panel("eleventh", WritingCheck, signals, cases)


def _twelfth() -> Panel:
    from ninth.state import empty
    from twelfth.explore import explore
    from twelfth.invariants import RecordCheck, check_records

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_records(explore(empty(), 2, 5)))

    cases: dict[str, Mutation] = {
        "not_determined_by_rel": lambda: _one("twelfth.invariants.record_determined_by_rel", lambda *_a: False),
        "nonempty_restored": lambda: _one("twelfth.invariants.restores_listed", lambda *_a: True),
        "empty_not_restored_isolated": lambda: _one("twelfth.invariants.restores_listed", lambda *_a: False),
        "swap_mismatch": lambda: _one("twelfth.invariants.swap", lambda s: s),
    }
    return Panel("twelfth", RecordCheck, signals, cases)


def _thirteenth() -> Panel:
    from ninth.state import empty
    from thirteenth.coarse import coarse as real_coarse
    from thirteenth.explore import explore
    from thirteenth.invariants import CoarseCheck, check_coarses

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_coarses(explore(empty(), 3, 6)))

    def coarse_of_empty() -> Any:
        fixed = real_coarse(empty())
        return everywhere("thirteenth", "coarse", lambda _s: fixed)

    cases: dict[str, Mutation] = {
        "not_sum": coarse_of_empty,
        "not_size": coarse_of_empty,
        "not_swap": lambda: _one("thirteenth.invariants.swap_keeps_coarse", lambda _s: False),
        "determines_when_asserted": lambda: _one("thirteenth.invariants.determines", lambda _s: True),
        "not_determines_when_empty": lambda: _one("thirteenth.invariants.determines", lambda _s: False),
        "splits_mismatch": lambda: _one("thirteenth.invariants.splits", lambda _s: -1),
        "add_r_s_fail": lambda: _both(
            ("thirteenth.invariants.add_r_or_s_same_coarser", lambda *_a: False),
            ("thirteenth.invariants.same_coarser", lambda *_a: False),
        ),
    }
    return Panel("thirteenth", CoarseCheck, signals, cases)


def _sixteenth() -> Panel:
    from fourteenth.leftover import leftover_nothing, leftover_pair
    from sixteenth.changes import Change16, Kind, changes16 as real_changes
    from sixteenth.explore import explore16
    from sixteenth.invariants import RecordCheck, check_records
    from sixteenth.state import add_assertion16, admit16, empty16

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_records(explore16(empty16(), 2, 4)))

    def extra_admission() -> Any:
        def wrong(rs: Any) -> Any:
            listed = real_changes(rs)
            return (*listed, Change16(Kind.ADD_ASSERTION, "r", 0, 0, True)) if rs.n >= 1 else listed

        return _one("sixteenth.invariants.changes16", wrong)

    cases: dict[str, Mutation] = {
        # the potential: a constant leaves every change unmoved, and every round off
        "potential_not_moved_by_one": lambda: _one("sixteenth.invariants.potential", lambda _rs: 0),
        "round_not_potential": lambda: _one("sixteenth.invariants.potential", lambda _rs: 0),
        # the direction rule: calling every change a raise makes admissions and identifications disagree
        "direction_mismatch": lambda: _one("sixteenth.invariants.raises_potential", lambda _c: True),
        # the mass: a falling measure fails on every direct addition
        "mass_fell": lambda: _one("sixteenth.invariants.mass", lambda rs: -(rs.state.m + rs.record_total)),
        "diagonal_mass_fell": lambda: _one("sixteenth.invariants.diag_mass", lambda rs: -rs.diagonal_mass),
        # the identity: an admission that forgets to consume the leftover
        "same_relation_not_identity": lambda: _one("sixteenth.invariants.admit16", add_assertion16),
        # the other relation: a canonical form that collapses everything, or a direct addition that consumes
        "other_relation_same_as_start": lambda: _one("sixteenth.invariants.canonical16", lambda rs: rs.n),
        "other_relation_same_as_direct": lambda: _one("sixteenth.invariants.add_assertion16", admit16),
        # the writings, perturbed at every binding site
        "admission_left_something": lambda: everywhere("sixteenth", "leftover_of16", lambda _s, _c: leftover_pair(0, 0)),
        "writing_not_the_fourteenth": lambda: everywhere("sixteenth", "leftover_of16", lambda _s, _c: leftover_nothing()),
        "unadmitted_asserted": lambda: _one("fourteenth.leftover.LeftWriting.is_assertion", lambda self: True),
        # the listing: an admission of a pair nobody recorded
        "admissions_not_recorded": extra_admission,
    }
    return Panel("sixteenth", RecordCheck, signals, cases)


def _eighteenth() -> Panel:
    from eighteenth.evidence import WritingCheck, audit
    from xry.state import Sameness, given, rewrite

    def signals() -> frozenset[str]:
        start = given(False, Sameness.ANCHORED)
        return _nonempty_lists(audit([start], start, rewrite(start, (1, 0))))

    cases: dict[str, Mutation] = {
        "writings_called_the_same": lambda: _one(
            "eighteenth.evidence.same_written", lambda _left, _right: True
        ),
        "orbit_formula_fails": lambda: _one(
            "eighteenth.evidence.orbit_splits_factorial", lambda _state: False
        ),
    }
    return Panel("eighteenth", WritingCheck, signals, cases)
def _seventeenth() -> Panel:
    from xry.changes import Answer, AnswerKind
    from xry.state import Sameness, State

    from seventeenth.evidence import LoopCheck, check_bounds
    from seventeenth.explore import Closure, closure_unobstructed as real_unobstructed
    from seventeenth.explore import with_loop
    from seventeenth.loop import obstructed_m1

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_bounds(2, 3))

    def only_start(start: State, bound: int, rounds: int, keep_log: bool = False) -> Closure:
        del bound, rounds, keep_log
        return Closure(depth={start: 0}, frontier=())

    def extra(start: State, bound: int, rounds: int, keep_log: bool = False) -> Closure:
        got = real_unobstructed(start, bound, rounds, keep_log)
        for bra in (False, True):
            for sameness in Sameness:
                got.depth[with_loop(bra, sameness)] = 1
        return got

    def bad_remove(state: State, change: object) -> tuple[Answer, ...]:
        del change
        return (Answer(AnswerKind.REMOVE_OBSTRUCTION, (), True, state),)

    def bad_refuse(state: State, change: object) -> tuple[Answer, ...]:
        del change
        return ()

    cases: dict[str, Mutation] = {
        "replace_has_xrx": lambda: _one("seventeenth.evidence.has_xrx", lambda _state: True),
        "replace_not_base": lambda: _one(
            "seventeenth.evidence.closure_unobstructed",
            lambda start, bound, rounds, keep_log=False: Closure(depth={}, frontier=()),
        ),
        "replace_cost_mismatch": lambda: _one("seventeenth.evidence.cost", lambda _state, _bra: -1),
        "replace_not_formula": lambda: _one(
            "seventeenth.evidence.by_cost", lambda _bound, _rounds, _bra, _sameness: set()
        ),
        "perform_misses_witness": lambda: _one("seventeenth.evidence.closure_perform", only_start),
        "perform_cost_not_above": lambda: _one("seventeenth.evidence.cost", lambda _state, _bra: 0),
        "m_disagree_loopfree": lambda: _one("seventeenth.evidence.outcome_has_xrx", lambda _state, _change: True),
        "m_agree_on_loop": lambda: _one(
            "seventeenth.evidence.outcome_has_xrx", lambda state, change: obstructed_m1(state, change)
        ),
        "remove_first_differs": lambda: _one("seventeenth.evidence.answers", bad_remove),
        "refusal_changes_something": lambda: _one("seventeenth.evidence.answers", bad_refuse),
        "loop_beginning_in_replace": lambda: _one("seventeenth.evidence.closure_unobstructed", extra),
        "loop_beginning_not_in_perform": lambda: _one("seventeenth.evidence.closure_perform", only_start),
    }
    return Panel("seventeenth", LoopCheck, signals, cases)


def panels() -> list[Panel]:
    return [
        _tenth(),
        _eleventh(),
        _twelfth(),
        _thirteenth(),
        _fourteenth(),
        _fifteenth(),
        _sixteenth(),
        _eighteenth(),
        _seventeenth(),
    ]


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    argparse.ArgumentParser(prog="check_mutation_bite", description=__doc__).parse_args(argv)

    ps = panels()
    problems = [p for panel in ps for p in check_panel(panel)]
    fields = sum(len(disagreement_fields(panel.check_class)) for panel in ps)
    if not problems:
        print(f"mutation-bite gate clean: {fields} disagreement fields across {len(ps)} derivations, each bites under its mutation")
        return 0
    for problem in problems:
        print(f"FAIL: {problem}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
