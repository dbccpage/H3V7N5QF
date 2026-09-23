from __future__ import annotations

from pathlib import Path

import pytest

from xry.changes import Answer, AnswerKind, Change, Kind
from xry.cost import cost
from xry.explore import explore
from xry.state import Sameness, State, canonical, given

from seventeenth.explore import (
    Closure,
    added_loop,
    by_cost,
    closure,
    closure_perform,
    closure_unobstructed,
    identified,
    loopfree_states,
    loopy_witness,
    with_loop,
    with_other_loop,
)
from seventeenth.loop import has_xrx, obstructed_m1, outcome_has_xrx, readings_agree


def test_has_xrx_and_the_two_readings() -> None:
    start = given(False, Sameness.ANCHORED)
    assert not has_xrx(start)
    assert readings_agree(start)
    assert has_xrx(added_loop(False, Sameness.ANCHORED))
    state, change = loopy_witness()
    assert has_xrx(state)
    assert not obstructed_m1(state, change)
    assert outcome_has_xrx(state, change)
    assert not readings_agree(state)
    assert readings_agree(given(True, Sameness.FREE))


def test_replace_matches_the_base_and_has_no_loop() -> None:
    for bra in (False, True):
        for sameness in Sameness:
            start = given(bra, sameness)
            base = explore(start, 2, 4)
            own = closure_unobstructed(start, 2, 4)
            assert own.depth == base.depth
            assert all(not has_xrx(state) for state in own.depth)
            assert by_cost(2, 4, bra, sameness) == set(own.depth)


def test_perform_reaches_the_witnesses_and_the_formula_does_not_bound_them() -> None:
    for bra in (False, True):
        for sameness in Sameness:
            start = given(bra, sameness)
            reached = closure_perform(start, 2, 4)
            witness = identified(bra, sameness)
            assert has_xrx(witness)
            assert reached.depth[witness] == 1
            assert cost(witness, bra) > 1
            assert with_loop(bra, sameness) in reached.depth
            # Adding `ara` to what is given is the `ara` beginning itself.
            assert added_loop(bra, sameness) == with_loop(bra, sameness)
            assert with_other_loop(bra, sameness) in reached.depth
            assert has_xrx(with_other_loop(bra, sameness))
            assert with_loop(bra, sameness) not in closure_unobstructed(start, 2, 4).depth
            assert with_other_loop(bra, sameness) not in closure_unobstructed(start, 2, 4).depth


def test_remove_first_matches_perform_first() -> None:
    from seventeenth.evidence import _remove_first_differs, _refusal_changes

    for bra in (False, True):
        for sameness in Sameness:
            assert not _remove_first_differs(bra, sameness)
            assert not _refusal_changes(bra, sameness)


def test_closure_rejects_a_bound_below_the_start_and_logs() -> None:
    start = given(False, Sameness.ANCHORED)
    with pytest.raises(ValueError):
        closure(start, 1, 1, enter_obstructed=True)
    with pytest.raises(ValueError):
        closure(start, 2, -1, enter_obstructed=False)
    logged = closure_perform(start, 2, 1, keep_log=True)
    assert logged.log
    assert any(record.obstructed and record.entered for record in logged.log)
    replaced = closure_unobstructed(start, 2, 1, keep_log=True)
    assert any(record.obstructed and not record.entered for record in replaced.log)
    assert any("terms" in line for line in replaced.frontier)


def test_closure_reports_what_the_round_bound_left_unexpanded() -> None:
    start = given(False, Sameness.FREE)
    cut = closure_unobstructed(start, 2, 1)
    assert cut.unexpanded
    assert set(cut.unexpanded) == {state.key() for state, depth in cut.depth.items() if depth == 1}
    assert closure_unobstructed(start, 2, 20).unexpanded == ()
    assert closure_perform(start, 2, 0).unexpanded == (canonical(start).key(),)


def test_loopfree_enumeration_skips_the_diagonal() -> None:
    states = loopfree_states(2, Sameness.FREE)
    assert states
    assert all(not has_xrx(state) for state in states)
    with pytest.raises(ValueError):
        loopfree_states(0, Sameness.FREE)
    anchored = loopfree_states(1, Sameness.ANCHORED)
    assert anchored == {canonical(State.of(1, [], (0, 0)))}


def test_one_term_loop_is_not_loopfree() -> None:
    loop = identified(False, Sameness.FREE)
    assert loop.n == 1 and has_xrx(loop)
    assert loop not in loopfree_states(1, Sameness.FREE)


def test_answer_patches_are_visible(monkeypatch: pytest.MonkeyPatch) -> None:
    """The two branches of the answer checks, driven without the whole report."""
    from seventeenth import evidence

    def no_remove(state: State, change: Change) -> tuple[Answer, ...]:
        del change
        return (Answer(AnswerKind.REFUSE, (), False, state),)

    monkeypatch.setattr(evidence, "answers", no_remove)
    assert evidence._remove_first_differs(False, Sameness.ANCHORED)

    def bad_remove(state: State, change: Change) -> tuple[Answer, ...]:
        del change
        return (
            Answer(AnswerKind.REMOVE_OBSTRUCTION, (), True, state),
            Answer(AnswerKind.REFUSE, (), False, state),
        )

    monkeypatch.setattr(evidence, "answers", bad_remove)
    assert evidence._remove_first_differs(False, Sameness.ANCHORED)
    assert not evidence._refusal_changes(False, Sameness.ANCHORED)

    def bad_refuse(state: State, change: Change) -> tuple[Answer, ...]:
        del change
        return (Answer(AnswerKind.REFUSE, (), True, state),)

    monkeypatch.setattr(evidence, "answers", bad_refuse)
    assert evidence._refusal_changes(False, Sameness.ANCHORED)

    def two_refuses(state: State, change: Change) -> tuple[Answer, ...]:
        del change
        return (Answer(AnswerKind.REFUSE, (), False, state), Answer(AnswerKind.REFUSE, (), False, state))

    monkeypatch.setattr(evidence, "answers", two_refuses)
    assert evidence._refusal_changes(False, Sameness.ANCHORED)

    other = State.of(2, [], (0, 1))

    def moved(state: State, change: Change) -> tuple[Answer, ...]:
        del state, change
        return (Answer(AnswerKind.REFUSE, (), False, other),)

    monkeypatch.setattr(evidence, "answers", moved)
    assert evidence._refusal_changes(False, Sameness.ANCHORED)


def test_identify_is_a_real_change() -> None:
    start = given(False, Sameness.ANCHORED)
    out = closure_perform(start, 2, 1)
    assert Change(Kind.IDENTIFY, 0, 1).kind is Kind.IDENTIFY
    assert any(state.n == 1 for state in out.depth)
    assert Closure(depth={}, frontier=()).frontier == ()
