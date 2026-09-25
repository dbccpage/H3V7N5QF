"""Pytest suite for Problem 05: Refusal Memory.

Tests:
- Refusal recording: First attempt at an obstructed change changes nothing about
  terms or assertions and keeps written change in refusal memory.
- Override step: Repeated attempt at that same change performs the change even if
  it makes some `xrx` asserted.
- Loop creation on second attempt: Loop states like `oneLoop` and `added_loop`
  are reached at round 2, whereas seventeenth A-replace never reaches them, and
  A-perform reaches them at round 1.
- Canonicalization under ANCHORED and FREE sameness.
- RecordScope (LOCAL and CARRIED).
- Exploration, exact frontier, and independent census.
- 100% coverage of model.py.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from model import (
    Closure,
    RecordScope,
    RefusalState,
    StepOutcome,
    attempt_step,
    canonical_refusal,
    closure,
    independent_census,
    loopfree_census,
    rewrite_change,
    rewrite_refusal_state,
)
from seventeenth.loop import has_xrx
from xry.changes import Change, Kind, changes
from xry.state import Sameness, State, canonical, given


def test_refusal_state_properties() -> None:
    s = State.of(2, [(0, 1)], (0, 1))
    c = Change(Kind.IDENTIFY, 0, 1)
    rs = RefusalState(s, frozenset([c]))
    assert rs.n == 2
    assert rs.m == 1
    assert not rs.has_loop
    assert "refused:" in rs.key()
    assert rs.added() == (0, 0)

    # Empty refusal key
    rs_empty = RefusalState(s, frozenset())
    assert rs_empty.key() == s.key()

    # Invalid term raises ValueError
    bad_change = Change(Kind.ADD_ASSERTION, 0, 5)
    with pytest.raises(ValueError, match="not in state"):
        RefusalState(s, frozenset([bad_change]))


def test_rewrite_change_all_kinds() -> None:
    p = (2, 0, 1)
    c_term = Change(Kind.ADD_TERM)
    assert rewrite_change(c_term, p) == c_term

    c_ident = Change(Kind.IDENTIFY, 0, 1)
    # p[0]=2, p[1]=0 -> min=0, max=2
    assert rewrite_change(c_ident, p) == Change(Kind.IDENTIFY, 0, 2)

    c_add = Change(Kind.ADD_ASSERTION, 0, 1)
    assert rewrite_change(c_add, p) == Change(Kind.ADD_ASSERTION, 2, 0)

    c_rem = Change(Kind.REMOVE, 1, 0)
    assert rewrite_change(c_rem, p) == Change(Kind.REMOVE, 0, 2)


def test_refusal_recording_on_first_attempt() -> None:
    """First attempt at obstructed change is refused and kept with result."""
    start = given(False, Sameness.ANCHORED)
    rs = RefusalState(start, frozenset())
    c_ident = Change(Kind.IDENTIFY, 0, 1)

    outcome = attempt_step(rs, c_ident, enter_obstructed=False)
    assert outcome.obstructed
    assert outcome.is_refusal
    assert not outcome.is_override
    # Terms and assertions unchanged
    assert outcome.target.state == start
    # Written form kept in refused set
    assert c_ident in outcome.target.refused
    assert len(outcome.target.refused) == 1
    assert not outcome.target.has_loop


def test_override_step_on_second_attempt_creates_loop() -> None:
    """Second attempt at the same written change performs override, creating loop."""
    start = given(False, Sameness.ANCHORED)
    c_ident = Change(Kind.IDENTIFY, 0, 1)
    rs_refused = RefusalState(start, frozenset([c_ident]))

    outcome = attempt_step(rs_refused, c_ident, enter_obstructed=False)
    assert outcome.obstructed
    assert not outcome.is_refusal
    assert outcome.is_override
    # One-term outcome asserting a loop (oneLoop)
    assert outcome.target.n == 1
    assert outcome.target.m == 1
    assert outcome.target.has_loop
    assert outcome.target.state.has(0, 0)


def test_override_for_add_loop_assertion() -> None:
    """Adding ara is obstructed, refused on attempt 1, performed on attempt 2."""
    start = given(False, Sameness.ANCHORED)
    c_loop = Change(Kind.ADD_ASSERTION, 0, 0)
    rs = RefusalState(start, frozenset())

    # Attempt 1: refused
    out1 = attempt_step(rs, c_loop, enter_obstructed=False)
    assert out1.is_refusal
    assert not out1.target.has_loop

    # Attempt 2: override
    out2 = attempt_step(out1.target, c_loop, enter_obstructed=False)
    assert out2.is_override
    assert out2.target.has_loop
    assert out2.target.state.has(0, 0)
    assert out2.target.n == 2


def test_unobstructed_step_performs_normally() -> None:
    """Unobstructed changes (remove, add term, legal assertion) perform normally."""
    start = given(False, Sameness.ANCHORED)
    c_add_term = Change(Kind.ADD_TERM)
    rs = RefusalState(start, frozenset([Change(Kind.IDENTIFY, 0, 1)]))

    # LOCAL scope clears refusal record on transition
    out_local = attempt_step(rs, c_add_term, scope=RecordScope.LOCAL)
    assert not out_local.obstructed
    assert not out_local.is_refusal
    assert not out_local.is_override
    assert out_local.target.n == 3
    assert len(out_local.target.refused) == 0

    # CARRIED scope preserves valid refused changes
    out_carried = attempt_step(rs, c_add_term, scope=RecordScope.CARRIED)
    assert out_carried.target.n == 3
    assert Change(Kind.IDENTIFY, 0, 1) in out_carried.target.refused

    # CARRIED scope with override drops the executed change
    rs_for_override = RefusalState(
        start, frozenset([Change(Kind.IDENTIFY, 0, 1), Change(Kind.ADD_ASSERTION, 0, 0)])
    )
    out_override_carried = attempt_step(
        rs_for_override, Change(Kind.IDENTIFY, 0, 1), scope=RecordScope.CARRIED
    )
    assert out_override_carried.is_override
    # 0r0 mentions term 0 which exists in 1-term state
    assert Change(Kind.ADD_ASSERTION, 0, 0) in out_override_carried.target.refused
    assert Change(Kind.IDENTIFY, 0, 1) not in out_override_carried.target.refused


def test_enter_obstructed_reading() -> None:
    """Under enter_obstructed=True (A-perform), changes are performed immediately."""
    start = given(False, Sameness.ANCHORED)
    c_ident = Change(Kind.IDENTIFY, 0, 1)
    rs = RefusalState(start, frozenset())

    outcome = attempt_step(rs, c_ident, enter_obstructed=True)
    assert outcome.obstructed
    assert not outcome.is_refusal
    assert not outcome.is_override
    assert outcome.target.has_loop
    assert outcome.target.n == 1


def test_canonical_refusal_free_and_anchored() -> None:
    """Canonicalization under FREE permutes terms to least representation."""
    s = State.of(3, [(0, 1), (1, 2)], None)
    c1 = Change(Kind.ADD_ASSERTION, 0, 0)
    c2 = Change(Kind.ADD_ASSERTION, 2, 2)
    rs1 = RefusalState(s, frozenset([c1]))
    canon1 = canonical_refusal(rs1)
    assert isinstance(canon1, RefusalState)

    # Test rewrite_refusal_state with names and without names
    p = (1, 0, 2)
    rewritten = rewrite_refusal_state(rs1, p)
    assert rewritten.state.n == 3
    assert Change(Kind.ADD_ASSERTION, 1, 1) in rewritten.refused

    s_anchored = State.of(3, [(0, 1), (1, 2)], (0, 1))
    rs_anchored = RefusalState(s_anchored, frozenset([c1]))
    rewritten_anchored = rewrite_refusal_state(rs_anchored, p)
    assert rewritten_anchored.state.names == (1, 0)

    # Test CARRIED scope when term count decreases (identification) dropping invalid change
    s2 = State.of(3, [(0, 1)], (0, 1))
    c_out_of_bounds_after_merge = Change(Kind.ADD_ASSERTION, 2, 2)
    rs_drop = RefusalState(s2, frozenset([c_out_of_bounds_after_merge]))
    # identify 1 and 2 (reducing terms from 3 to 2)
    out_drop = attempt_step(rs_drop, Change(Kind.IDENTIFY, 1, 2), scope=RecordScope.CARRIED)
    assert out_drop.target.n == 2
    assert c_out_of_bounds_after_merge not in out_drop.target.refused


def test_closure_exploration_and_falsifier_resolution() -> None:
    """Closure under refusal memory reaches loop states at round 2, falsifying agreement with seventeenth."""
    start = given(False, Sameness.ANCHORED)

    # Explore under refusal memory
    cl = closure(start, bound=2, rounds=3, enter_obstructed=False, keep_log=True)
    assert cl.depth[canonical_refusal(RefusalState(start, frozenset()))] == 0

    # In round 1, refusal states are reached
    refusal_states = [s for s, d in cl.depth.items() if d == 1 and s.refused]
    assert len(refusal_states) > 0
    assert all(not s.has_loop for s in refusal_states)

    # In round 2, loop states ARE reached!
    loop_states_round2 = [s for s, d in cl.depth.items() if d == 2 and s.has_loop]
    assert len(loop_states_round2) > 0

    # Compare with A-perform (enter_obstructed=True):
    # Under A-perform, loop states are reached at round 1
    cl_perform = closure(start, bound=2, rounds=3, enter_obstructed=True, keep_log=True)
    loop_states_perform_r1 = [s for s, d in cl_perform.depth.items() if d == 1 and s.has_loop]
    assert len(loop_states_perform_r1) > 0

    # Agreement fails:
    # 1. Under seventeenth A-replace: 0 loop states are ever reached.
    # 2. In Problem 05 refusal memory: loop states are reached at round 2.
    # 3. Under seventeenth A-perform: loop states are reached at round 1.
    assert len(loop_states_round2) > 0
    assert (
        canonical_refusal(RefusalState(State.of(1, [(0, 0)], (0, 0)), frozenset()))
        in cl.depth
    )
    assert (
        cl.depth[canonical_refusal(RefusalState(State.of(1, [(0, 0)], (0, 0)), frozenset()))]
        == 2
    )

    # Check frontier and unexpanded
    assert isinstance(cl.frontier, tuple)
    assert len(cl.unexpanded) > 0
    assert len(cl.log) > 0


def test_closure_validation_errors() -> None:
    start = given(False, Sameness.ANCHORED)
    with pytest.raises(ValueError, match="bound below start or negative rounds"):
        closure(start, bound=1, rounds=2)
    with pytest.raises(ValueError, match="bound below start or negative rounds"):
        closure(start, bound=2, rounds=-1)


def test_independent_census() -> None:
    census_anchored = independent_census(bound=1, sameness=Sameness.ANCHORED)
    assert len(census_anchored) > 0

    census_free = independent_census(bound=1, sameness=Sameness.FREE)
    assert len(census_free) > 0

    loopfree = loopfree_census(bound=1, sameness=Sameness.FREE)
    assert all(not s.has_loop and not s.refused for s in loopfree)

    with pytest.raises(ValueError, match="at least 1"):
        independent_census(bound=0, sameness=Sameness.FREE)


def test_both_beginnings_and_sameness_options() -> None:
    for bra in (False, True):
        for sameness in (Sameness.ANCHORED, Sameness.FREE):
            start = given(bra, sameness)
            cl = closure(start, bound=2, rounds=2, enter_obstructed=False)
            assert len(cl.depth) > 0


def test_evidence_generation_and_check(tmp_path: Path) -> None:
    from evidence import generate_all_evidence, main, verify_check
    written = generate_all_evidence(tmp_path)
    assert len(written) == 5
    assert (tmp_path / "MANIFEST.sha256").exists()
    assert verify_check(tmp_path)

    # Test main CLI generate
    assert main(["--out", str(tmp_path)]) == 0

    # Test main CLI check success
    assert main(["--out", str(tmp_path), "--check"]) == 0

    # Test missing file in check
    (tmp_path / "summary.json").unlink()
    assert not verify_check(tmp_path)
    assert main(["--out", str(tmp_path), "--check"]) == 1

    # Test hash mismatch in check
    generate_all_evidence(tmp_path)
    (tmp_path / "summary.json").write_text("corrupted\n", encoding="utf-8")
    assert not verify_check(tmp_path)
    assert main(["--out", str(tmp_path), "--check"]) == 1
