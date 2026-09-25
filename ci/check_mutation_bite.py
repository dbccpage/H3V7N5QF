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


def _eighteenth() -> Panel:
    from eighteenth.evidence import WritingCheck, audit
    from eighteenth.explore import explore_written
    from xry.state import Sameness, given, rewrite

    def signals() -> frozenset[str]:
        start = given(False, Sameness.ANCHORED)
        depth = explore_written(start, 2, 4).depth
        return _nonempty_lists(audit(depth, False, start, rewrite(start, (1, 0))))

    cases: dict[str, Mutation] = {
        "writings_called_the_same": lambda: _one(
            "eighteenth.evidence.same_written", lambda _left, _right: True
        ),
        "orbit_formula_fails": lambda: _one(
            "eighteenth.evidence.orbit_splits_factorial", lambda _state: False
        ),
        "rounds_below_the_base_cost": lambda: _one("eighteenth.evidence.cost", lambda _state, _bra: 99),
    }
    return Panel("eighteenth", WritingCheck, signals, cases)


def _nineteenth() -> Panel:
    from nineteenth.evidence import PartialCheck, audit
    from nineteenth.explore import explore_partial as real_partial
    from xry.state import Sameness, State

    def signals() -> frozenset[str]:
        return _nonempty_lists(audit(False, Sameness.ANCHORED, 2, 2))

    def plant(cooccur_state: State | None, broad_states: tuple[State, ...], performed: bool) -> Any:
        def wrong(start: Any, bound: int, rounds: int = 12, cooccur_only: bool = False, keep_log: bool = False) -> Any:
            del keep_log
            exp = real_partial(start, bound, rounds, cooccur_only, False)
            exp.depth = dict(exp.depth)
            if cooccur_only:
                if cooccur_state is not None:
                    exp.depth[cooccur_state] = 1
                if performed:
                    exp.performed_partials = 1
            else:
                for state in broad_states:
                    exp.depth[state] = 1
            return exp

        return _one("nineteenth.evidence.explore_partial", wrong)

    cases: dict[str, Mutation] = {
        "sets_differ": lambda: plant(State.of(2, [(1, 0)], (1, 0)), (), False),
        "extra_beyond_base": lambda: plant(None, (State.of(3, [], (0, 1)),), False),
        "term_dropped": lambda: plant(None, (State.of(1, [], (0, 0)),), False),
        "cooccur_performed": lambda: plant(None, (), True),
        "obstruction_not_between": lambda: _one("nineteenth.evidence.obstructed", lambda _state, _partial: False),
        "removal_answer_outside": lambda: _one(
            "nineteenth.evidence.canonical", lambda _state: State.of(3, [], (0, 0))
        ),
    }
    return Panel("nineteenth", PartialCheck, signals, cases)


def _twentieth() -> Panel:
    from twentieth.evidence import OrderCheck, audit
    from twentieth.order import _bfs as real_bfs
    from twentieth.order import additions_priority as real_priority
    from xry.state import State

    def signals() -> frozenset[str]:
        return _nonempty_lists(audit(False, 2, 4))

    def shorten(drop_bound: bool, only_root: bool) -> Any:
        def wrong(start: Any, bound: int, rounds: int, by_additions: bool) -> dict[State, int]:
            depth = real_bfs(start, bound, rounds, by_additions)
            if drop_bound and by_additions:
                return {state: depth[state] for state in depth if state.n < bound}
            if only_root and not by_additions:
                root = min(depth, key=lambda state: depth[state])
                return {root: 0}
            return depth

        return _one("twentieth.evidence._bfs", wrong)

    cases: dict[str, Mutation] = {
        "layer_mismatch": lambda: shorten(True, False),
        "frontier_mismatch": lambda: shorten(True, False),
        "differs_from_base": lambda: shorten(False, True),
        "additions_track_rounds": lambda: _one("twentieth.evidence.rankings_differ", lambda _depth: None),
        "o2_closure_differs": lambda: _one(
            "twentieth.evidence.additions_priority",
            lambda start, bound, _expansions: real_priority(start, bound, 1),
        ),
    }
    return Panel("twentieth", OrderCheck, signals, cases)


def _twentyfirst() -> Panel:
    from twentyfirst.evidence import RefusalCheck, audit
    from xry.state import Sameness

    def signals() -> frozenset[str]:
        return _nonempty_lists(audit(False, Sameness.ANCHORED, 2, 4))

    cases: dict[str, Mutation] = {
        # Perform what the seed refuses: the refusing closure leaves the base's.
        "outside_the_base": lambda: _one("twentyfirst.refusal.refused", lambda _outcome: False),
        "answer_buys_a_result": lambda: _one("twentyfirst.evidence.answer_is_new", lambda _got, _depth: True),
        "stopped_at_the_start": lambda: _one("twentyfirst.evidence.has_unobstructed", lambda _state: False),
    }
    return Panel("twentyfirst", RefusalCheck, signals, cases)


def _twentysecond() -> Panel:
    from ninth.explore import explore as real_ninth
    from seventh.explore import explore as real_seventh
    from twentysecond.changes import Change, Kind, perform
    from twentysecond.evidence import JointCheck, audit

    def signals() -> frozenset[str]:
        return _nonempty_lists(audit(2, 4, 4, 1, 2))

    def fewer_rounds(real: Callable[..., Any]) -> Callable[..., Any]:
        def wrong(start: Any, bound: int, rounds: int = 100, keep_log: bool = False) -> Any:
            return real(start, bound, max(rounds - 1, 0), keep_log)

        return wrong

    def add_r_twice(state: Any, x: int, y: int) -> Any:
        once = perform(state, Change(Kind.ADD_ASSERTION, "r", x, y))
        return perform(once, Change(Kind.ADD_ASSERTION, "r", x, y))

    cases: dict[str, Mutation] = {
        # the cost formula against the rounds, and against every change
        "round_not_cost": lambda: _one("twentysecond.evidence.cost", lambda _s: -1),
        "cost_raised_by_more_than_one": lambda: _one("twentysecond.evidence.cost", lambda s: 5 * s.n),
        # the rule for what is recorded, computed from the excesses, against the outcome
        "record_move_mismatch": lambda: _one("twentysecond.evidence.predicted_move", lambda _s, _c: (9, 9)),
        # a removal from a state that is not plain, against the plain state's outcomes
        "removal_outside": lambda: _one("twentysecond.evidence.result_changes", lambda _s: ()),
        # the second addition of the other relation, replaced by the same relation again
        "undo_failed": lambda: _one("twentysecond.evidence.add_r_then_s", add_r_twice),
        "raising_not_addition": lambda: _one("twentysecond.evidence.is_addition", lambda _c: False),
        # the independent counts and closed forms
        "count_mismatch": lambda: _one("twentysecond.evidence.counts_within", lambda _b, _r: {}),
        "two_term_mismatch": lambda: _one("twentysecond.evidence.two_term_round_count", lambda _r: -1),
        "one_term_not_one_sequence": lambda: _one(
            "twentysecond.evidence.count_shortest_sequences", lambda e: {s: 2 for s in e.depth}
        ),
        # the exchange: an identity in its place negates no excess
        "exchange_mismatch": lambda: _one("twentysecond.evidence.swap", lambda s: s),
        # the earlier derivations' explorations, cut short by a round
        "seventh_mismatch": lambda: _one("twentysecond.evidence.explore_seventh", fewer_rounds(real_seventh)),
        "read_back_mismatch": lambda: _one("twentysecond.evidence.read_back", lambda _s: None),
        "ninth_mismatch": lambda: _one("twentysecond.evidence.explore_ninth", fewer_rounds(real_ninth)),
        "reach_mismatch": lambda: _one("twentysecond.evidence.reachable", lambda _s, _t: True),
        # the sameness: equality of writings in place of the seed's sameness
        "sameness_mismatch": lambda: _one("twentysecond.evidence.same", lambda s, t: s == t),
        "readings_mismatch": lambda: _one("twentysecond.evidence.cost_j2", lambda _k: -1),
    }
    return Panel("twentysecond", JointCheck, signals, cases)


def _twentythird() -> Panel:
    from ninth.explore import explore as real_ninth
    from twentysecond.explore import performed as real_performed
    from twentythird.embed import seventh_pair
    from twentythird.evidence import RaisingCheck, audit
    from twentythird.state import excess_table

    def signals() -> frozenset[str]:
        return _nonempty_lists(audit(2, 4, 4, 1, 3))

    def fewer_rounds(start: Any, bound: int, rounds: int = 100, keep_log: bool = False) -> Any:
        return real_ninth(start, bound, max(rounds - 1, 0), keep_log)

    def outcome_is_start(expl: Any) -> Any:
        return ((s, c, r, s) for s, c, r, _ in real_performed(expl))

    a, _ = seventh_pair()
    cases: dict[str, Mutation] = {
        # the cost by raising sets of terms against the rounds, the closed forms and the search
        "round_not_cost": lambda: _one("twentythird.evidence.cost", lambda _s: -1),
        "closed_form_mismatch": lambda: _one("twentythird.evidence.cost_closed", lambda _s: -5),
        # the states asserting the fewest found by raising, against those the exploration reached first
        "fewest_mismatch": lambda: _one("twentythird.evidence.fewest_states", lambda _s: []),
        "characterization_mismatch": lambda: _one("twentythird.evidence.set_moves_least", lambda _n, _t: True),
        "record_mismatch": lambda: _one("twentythird.evidence.record", lambda _s: (0, 0, 0)),
        # the sums kept by the sameness, against the mark of the result asserting nothing
        "nothing_mismatch": lambda: _one("twentythird.evidence.nothing_certificate", lambda _s: None),
        # the independent counts and closed forms
        "count_mismatch": lambda: _one("twentythird.evidence.counts_within", lambda _b, _r: {}),
        "two_term_mismatch": lambda: _one("twentythird.evidence.two_term_round_count", lambda _r: -1),
        # every change's outcome replaced by its start: the parity of the cost does not change
        "change_mismatch": lambda: _one("twentythird.evidence.performed", outcome_is_start),
        # outcomes read at their writing, not as results
        "respect_mismatch": lambda: _one("twentythird.evidence.outcome_key", lambda s, _c: (s.n, excess_table(s))),
        "plain_mismatch": lambda: _one("twentythird.evidence.plain_cost", lambda _s: -1),
        # the earlier derivations: the ninth's exploration cut short; the seventh's pair made one state
        "ninth_mismatch": lambda: _one("twentythird.evidence.explore_ninth", fewer_rounds),
        "seventh_mismatch": lambda: _one("twentythird.evidence.seventh_pair", lambda: (a, a)),
        "read_back_mismatch": lambda: _one("twentythird.evidence.read_back_direct", lambda _s: None),
        "reach_mismatch": lambda: _one("twentythird.evidence.reachable", lambda _s, _t: True),
        # the exchange: an identity in its place negates no excess
        "exchange_mismatch": lambda: _one("twentythird.evidence.swap", lambda s: s),
        # the search for the generated sameness with no joins at all
        "sameness_mismatch": lambda: _one("twentythird.evidence.steps_h1", lambda _s: iter(())),
        "readings_mismatch": lambda: _one("twentythird.evidence.cost_j3", lambda _s: -1),
    }
    return Panel("twentythird", RaisingCheck, signals, cases)


def _twentyfourth() -> Panel:
    from twentyfourth.evidence import FillCheck, audit
    from twentyfourth.explore import performed as real_performed
    from twentythird.explore import explore as real_twentythird
    from twentythird.state import excess_table

    def signals() -> frozenset[str]:
        return _nonempty_lists(audit(2, 4))

    def outcome_is_start(expl: Any) -> Any:
        return ((s, c, s, o) for s, c, _, o in real_performed(expl))

    def fewer_rounds(bound: int, rounds: int, keep_log: bool = False) -> Any:
        return real_twentythird(bound, max(rounds - 1, 0), keep_log)

    cases: dict[str, Mutation] = {
        # the cost (the twenty-third's plus the filled terms) against the rounds of results and states
        "round_not_cost": lambda: _one("twentyfourth.evidence.cost", lambda _s: -1),
        # the balance record read on every state against the one read from the mark
        "balance_mismatch": lambda: _one("twentyfourth.evidence.balance_record", lambda _s: (9, 9)),
        "tell_mismatch": lambda: _one("twentyfourth.evidence.tell_class", lambda _s: "nothing"),
        "record_mismatch": lambda: _one("twentyfourth.evidence.record23", lambda _s: (0, 0, 0)),
        # the independent counts and closed forms
        "count_mismatch": lambda: _one("twentyfourth.evidence.counts_within", lambda _b, _r: {}),
        "two_term_mismatch": lambda: _one("twentyfourth.evidence.two_term_round_count", lambda _r: -1),
        "sequences_mismatch": lambda: _one("twentyfourth.evidence.one_term_sequences", lambda _k, _t: -1),
        # every change's outcome replaced by its start
        "change_mismatch": lambda: _one("twentyfourth.evidence.performed", outcome_is_start),
        # outcomes read at their writing, not as results
        "respect_mismatch": lambda: _one(
            "twentyfourth.evidence.outcome_key", lambda s, _c: (s.n, excess_table(s.base), s.fills)
        ),
        # the twenty-third's run cut short
        "twentythird_mismatch": lambda: _one("twentyfourth.embed.explore23", fewer_rounds),
        "read_back_mismatch": lambda: _one("twentyfourth.evidence.read_back", lambda _k: None),
        "forget_mismatch": lambda: _one("twentyfourth.evidence.forget_key", lambda _k: (0, ())),
        "reach_mismatch": lambda: _one("twentyfourth.evidence.reachable", lambda _s, _t, _r: True),
        # the exchange: an identity in its place exchanges no record
        "exchange_mismatch": lambda: _one("twentyfourth.evidence.swap", lambda s: s),
        # the search for the generated sameness with no joins at all
        "sameness_mismatch": lambda: _one("twentyfourth.readings.fill_steps", lambda _s: iter(())),
        "readings_mismatch": lambda: _one("twentyfourth.evidence.cost_counted", lambda _s: -1),
        # the twenty-third's record question with every result kept by no term
        "record_question_mismatch": lambda: _one("twentyfourth.evidence.keeping_size", lambda _b: 0),
    }
    return Panel("twentyfourth", FillCheck, signals, cases)


def _twentyfifth() -> Panel:
    from twentyfifth.evidence import FillingCheck, audit
    from twentyfifth.explore import performed as real_performed
    from twentythird.explore import explore as real_explore23
    from twentythird.state import DState, excess

    def signals() -> frozenset[str]:
        return _nonempty_lists(audit(3, 6))

    def outcome_is_start(expl: Any) -> Any:
        return [(s, c, r, s) for s, c, r, _ in real_performed(expl)]

    def fewer_rounds(bound: int, rounds: int) -> Any:
        return real_explore23(bound, max(rounds - 1, 0))

    def with_a_loop(fs: Any) -> Any:
        r = list(fs.state.r)
        if fs.n:
            r[0] += 1
        return type(fs)(DState(fs.n, tuple(r), fs.state.s), fs.filled)

    cases: dict[str, Mutation] = {
        # the cost (the twenty-third's plus the filled triples) against the rounds; the rounds of the states
        "round_not_cost": lambda: _one("twentyfifth.evidence.cost", lambda _s: -1),
        "plain_mismatch": lambda: _one("twentyfifth.evidence.psi", lambda _s: -1),
        # the independent count and the twenty-third's two-term closed form
        "count_mismatch": lambda: _one("twentyfifth.evidence.counts_within", lambda _b, _r: {}),
        "two_term_mismatch": lambda: _one("twentyfifth.evidence.two_term_round_count", lambda _r: -1),
        # balance read on one pair instead of going round: not the same on every state of a result
        "record_mismatch": lambda: _one(
            "twentyfifth.evidence.balances", lambda fs, t: excess(fs.state, t[0], t[1]) == 0
        ),
        # the two records compared, against "some filled triple does not balance"
        "told_mismatch": lambda: _one("twentyfifth.evidence.record_differs_from_nothing", lambda _fs: False),
        "blind_mismatch": lambda: _one("twentyfifth.evidence.blind_by_description", lambda _s: False),
        "keeping_mismatch": lambda: _one("twentyfifth.evidence.keeping_sets_by_restriction", lambda _s: ()),
        "whether_mismatch": lambda: _one("twentyfifth.evidence.record", lambda fs: (fs.n, 0, 0)),
        "decide_mismatch": lambda: _one("twentyfifth.evidence.decides", lambda _n, _sub: True),
        # every change's outcome replaced by its start
        "change_mismatch": lambda: _one("twentyfifth.evidence.performed", outcome_is_start),
        # the twenty-third's exploration cut short by a round
        "embed_mismatch": lambda: _one("twentyfifth.evidence.explore23", fewer_rounds),
        "read_back_mismatch": lambda: _one("twentyfifth.evidence.read_back", lambda _fs: None),
        "reach_mismatch": lambda: _one("twentyfifth.evidence.reachable", lambda _s, _t: True),
        # the exchange replaced by adding a loop: another result, of another round
        "exchange_mismatch": lambda: _one("twentyfifth.evidence.swap25", with_a_loop),
        "readings_mismatch": lambda: _one("twentyfifth.evidence.i3_reach_failures", lambda _run: (1, 1)),
    }
    return Panel("twentyfifth", FillingCheck, signals, cases)


def panels() -> list[Panel]:
    return [
        _tenth(),
        _eleventh(),
        _twelfth(),
        _thirteenth(),
        _fourteenth(),
        _fifteenth(),
        _sixteenth(),
        _seventeenth(),
        _eighteenth(),
        _nineteenth(),
        _twentieth(),
        _twentyfirst(),
        _twentysecond(),
        _twentythird(),
        _twentyfourth(),
        _twentyfifth(),
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
