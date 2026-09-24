"""Unit tests for Problem 06 (Written Budget) Derivation.

Covers:
- BudgetedState invariants, validation, properties, canonical forms.
- Step consumption: strict budget decrement, stopping / identity at budget 0.
- Available changes and attempt recording.
- Full exploration to budget exhaustion.
- Independent census of budgeted states and verification.
- Comparison with parent Ninth derivation: wave counts, revisited states, termination.
- Falsifier and hypothesis resolution checks.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Ensure derivation directory is on sys.path
HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

# Ensure repo code/ directory is on sys.path
ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:
    sys.path.insert(0, str(ROOT / "code"))

from eighth.changes import Change, Kind  # noqa: E402
from ninth.state import DState, canonical as canonical9, empty as empty9  # noqa: E402
from model import (  # noqa: E402
    INITIAL_BUDGET,
    MAX_CHANGES,
    AttemptRecord,
    BudgetedState,
    ExplorationResult,
    attempt,
    available_changes,
    canonical_budgeted,
    census_by_budget,
    compare_with_parent,
    explore,
    independent_census_counts,
    initial_state,
    perform_change,
)


def test_initial_state() -> None:
    """The initial state has no terms, nothing asserted, and budget 4."""
    init = initial_state()
    assert init.budget == INITIAL_BUDGET
    assert init.budget == 4
    assert init.n == 0
    assert init.m == 0
    assert init.size == 0
    assert init.state == empty9()


def test_budgeted_state_validation() -> None:
    """Budget must be in 0..4 and state must carry no names."""
    valid_dstate = empty9()
    with pytest.raises(ValueError, match="Budget must be in 0..4"):
        BudgetedState(valid_dstate, -1)
    with pytest.raises(ValueError, match="Budget must be in 0..4"):
        BudgetedState(valid_dstate, 5)

    named_dstate = DState(1, (0,), (0,), (0, 0))
    with pytest.raises(ValueError, match="carries no names"):
        BudgetedState(named_dstate, 4)


def test_budgeted_state_canonical() -> None:
    """Canonical representation preserves budget and normalizes underlying state."""
    # Create non-canonical 2-term state: pair (0,1) is index 1; (1,0) is index 2.
    # Under permutation (0 1), index 1 becomes index 2.
    # canonical9 chooses the least representation.
    non_canon = DState(2, (0, 1, 0, 0), (0, 0, 0, 0))
    canon_state = canonical9(non_canon)
    assert non_canon != canon_state
    bstate = BudgetedState(non_canon, 3)
    canon_bstate = bstate.canonical()
    assert canon_bstate.budget == 3
    assert canon_bstate.state == canon_state

    # Calling canonical on already canonical state returns self
    assert canon_bstate.canonical() is canon_bstate


def test_available_changes() -> None:
    """Available changes are empty at budget 0 and non-empty otherwise."""
    init = initial_state()
    # At initial state (empty, budget 4), exactly 1 change: ADD_TERM
    avail = available_changes(init)
    assert len(avail) == 1
    assert avail[0].kind == Kind.ADD_TERM

    # At budget 0, available_changes returns empty tuple
    b0 = BudgetedState(empty9(), 0)
    assert available_changes(b0) == ()


def test_step_consumption_and_budget_decrement() -> None:
    """Each performed change strictly uses 1 budget unit."""
    s0 = initial_state()
    assert s0.budget == 4

    add_t = Change(Kind.ADD_TERM)
    rec1 = attempt(s0, add_t)
    assert rec1.performed
    assert rec1.budget_used == 1
    s1 = rec1.outcome
    assert s1.budget == 3
    assert s1.n == 1

    add_r = Change(Kind.ADD_ASSERTION, "r", 0, 0)
    rec2 = attempt(s1, add_r)
    assert rec2.performed
    assert rec2.budget_used == 1
    s2 = rec2.outcome
    assert s2.budget == 2
    assert s2.n == 1
    assert s2.m == 1


def test_attempt_at_budget_zero_changes_nothing() -> None:
    """When budget is 0, any attempt changes nothing and uses 0 budget."""
    s = BudgetedState(empty9(), 0)
    add_t = Change(Kind.ADD_TERM)

    # Via perform_change directly
    out = perform_change(s, add_t)
    assert out == s

    # Via attempt record
    rec = attempt(s, add_t)
    assert not rec.performed
    assert rec.budget_used == 0
    assert rec.outcome == s
    assert rec.source == s


def test_canonical_budgeted_helper() -> None:
    """Helper canonical_budgeted creates a canonical BudgetedState."""
    b = canonical_budgeted(empty9(), 2)
    assert b.budget == 2
    assert b.state == empty9()


def test_full_exploration() -> None:
    """Full exploration from (empty, 4) visits exactly 46 states across 5 waves."""
    expl = explore(term_bound=4, max_rounds=100)
    assert len(expl.depth) == 46
    assert len(expl.waves) == 5

    # Check state counts by budget
    counts = {b: len(states) for b, states in expl.by_budget.items()}
    expected = {4: 1, 3: 1, 2: 3, 1: 9, 0: 32}
    assert counts == expected

    # Budget 4 has depth 0, budget 3 has depth 1, ..., budget 0 has depth 4
    for bstate, d in expl.depth.items():
        assert d == INITIAL_BUDGET - bstate.budget

    # No frontier exits with term_bound=4
    assert len(expl.frontier) == 0

    # Attempts at budget 0 were tracked
    assert expl.attempts_at_budget_zero > 0
    assert expl.attempts_count > expl.performed_count


def test_exploration_with_tight_term_bound() -> None:
    """With term_bound=3, attempts to add a 4th term are flagged on frontier."""
    expl = explore(term_bound=3, max_rounds=100)
    assert len(expl.frontier) > 0
    for src, c in expl.frontier:
        assert c.kind == Kind.ADD_TERM
        assert src.n == 3


def test_exploration_with_max_rounds() -> None:
    """Limiting max_rounds truncates exploration accordingly."""
    expl = explore(max_rounds=2)
    assert len(expl.waves) == 3  # round 0, 1, 2
    assert len(expl.depth) == 1 + 1 + 3


def test_independent_census() -> None:
    """Independent mathematical census matches exploration counts at every budget."""
    census = independent_census_counts()
    census_alias = census_by_budget()
    assert census == census_alias
    assert census == {4: 1, 3: 1, 2: 3, 1: 9, 0: 32}
    assert sum(census.values()) == 46


def test_comparison_with_parent() -> None:
    """Parent comparison verifies wave sizes and revisited lower sizes."""
    expl = explore()
    comp = compare_with_parent(expl)
    assert comp["census_matches"] is True
    assert comp["total_budgeted_states"] == 46
    assert comp["max_steps"] == MAX_CHANGES

    # Check revisited states
    revisited = comp["revisited_lower_sizes"]
    assert isinstance(revisited, dict)
    # At budget 1 (k=3), 1 state is revisited at size 1: (terms=1, mults=0)
    assert revisited[1] == [(1, 0)]
    # At budget 0 (k=4), 3 states are revisited at size 2:
    # 2-term empty (2, 0), 1-term 0r0 (1, 1), 1-term 0s0 (1, 1)
    assert (2, 0) in revisited[0]
    assert (1, 1) in revisited[0]
    assert len(revisited[0]) == 3


def test_falsifier_vs_hypothesis_resolution() -> None:
    """Test resolution between hypothesis and falsifier.

    Falsifier claim:
    'At every recorded budget, the reachable states are the parent's states at the same round.'

    Under BFS discovery wave (where parent round k = states of cost k):
    - At round 1 (budget 3): parent wave = 1 state, budget 3 = 1 state. (Matches)
    - At round 2 (budget 2): parent wave = 3 states, budget 2 = 3 states. (Matches)
    - At round 3 (budget 1): parent wave = 8 states (all size 3).
      Budget 1 = 9 states (8 size 3 + 1 size 1).
      The sets of underlying states are NOT identical under BFS discovery wave!
    - At round 4 (budget 0): parent wave = 29 states (all size 4).
      Budget 0 = 32 states (29 size 4 + 3 size 2).
      The sets are NOT identical!
    - At round 5: parent reaches 104 states. Budgeted system reaches 0 states!
      Reachability terminates at budget 0.
    """
    expl = explore()

    # Budget 1 underlying states
    b1_states = {s.state for s in expl.by_budget[1]}
    assert len(b1_states) == 9

    # Check that 1-term empty is in budget 1 states
    one_term_empty = canonical9(DState(1, (0,), (0,)))
    assert one_term_empty in b1_states

    # In parent Ninth, 1-term empty has size 1, so in parent BFS depth is 1, not 3
    # Therefore under BFS discovery definition, the falsifier is refuted at round 3!
    assert any(s.n == 1 and s.m == 0 for s in b1_states)

    # Under k-step path reachability (Reach9 empty s k):
    # In Ninth, Reach9 empty s 3 holds for all 9 states (sizes 1 and 3).
    # However, beyond round 4 (k >= 5), parent reachability continues,
    # while budgeted reachability is strictly capped at 4 steps.
    assert set(expl.waves[-1]) == set(expl.by_budget[0])
    assert len(expl.waves[-1]) == len(expl.by_budget[0])
    # No wave 5
    assert len(expl.waves) == 5


def test_evidence_generation_and_check(tmp_path: Path) -> None:
    """Test evidence writing, manifest generation, and byte-identical check."""
    import evidence

    # Write evidence
    out_dir = tmp_path / "evidence"
    files = evidence.write_evidence(out_dir)
    assert len(files) == 5

    manifest = out_dir / "MANIFEST.sha256"
    assert manifest.exists()

    # Verify evidence succeeds
    ok, msg = evidence.verify_evidence(out_dir)
    assert ok is True
    assert "Byte-identical regeneration verified" in msg

    # Test missing manifest
    manifest.unlink()
    ok_no_man, msg_no_man = evidence.verify_evidence(out_dir)
    assert ok_no_man is False
    assert "Manifest missing" in msg_no_man

    # Re-write manifest
    evidence.write_evidence(out_dir)

    # Test missing evidence file
    (out_dir / "summary.json").unlink()
    ok_missing, msg_missing = evidence.verify_evidence(out_dir)
    assert ok_missing is False
    assert "Expected file summary.json missing" in msg_missing

    # Re-write and test corrupted file
    evidence.write_evidence(out_dir)
    (out_dir / "summary.json").write_text("corrupted content\n", encoding="utf-8")
    ok_corrupt, msg_corrupt = evidence.verify_evidence(out_dir)
    assert ok_corrupt is False
    assert "Byte mismatch in summary.json" in msg_corrupt


def test_evidence_cli(tmp_path: Path) -> None:
    """Test evidence CLI entrypoint with and without --check."""
    import evidence

    out_dir = tmp_path / "cli_ev"
    # CLI generate
    ret = evidence.main(["--out", str(out_dir)])
    assert ret == 0

    # CLI check pass
    ret_check = evidence.main(["--check", "--out", str(out_dir)])
    assert ret_check == 0

    # Corrupt file -> CLI check fail
    (out_dir / "summary.json").write_text("corrupt\n", encoding="utf-8")
    ret_check_fail = evidence.main(["--check", "--out", str(out_dir)])
    assert ret_check_fail == 1

