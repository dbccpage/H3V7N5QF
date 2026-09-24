"""Pytest suite for Problem 10: swap-as-change derivation.

Tests cover:
- Swap involution (swap . swap = id)
- Change kinds, additions, validation, and representations
- Fewest additions first ordering and chosen vs unchosen readings
- Performing changes and loop detection
- BFS exploration from empty state and exact equivalence with ninth
- Shortest path graph, cost reductions (strictly shorter paths with swap)
- Exact closed-form reduction formula verification
- Shortest sequence counts and 2-cycle properties
"""

from __future__ import annotations

from pathlib import Path

import evidence
import pytest
from eighth.state import DState, canonical, same
from ninth.state import empty, swap

from model import (
    KINDS,
    Attempt,
    Change,
    Exit,
    Exploration,
    Kind,
    all_canonical_states,
    all_pairs_shortest_paths,
    attempt,
    changes,
    compare_with_ninth,
    count_shortest_sequences,
    explore,
    find_cost_reductions,
    is_addition,
    is_change,
    makes_some_loop,
    order,
    perform,
    transition_graph,
    verify_swap_reduction_formula,
)


def test_swap_involution() -> None:
    """Swap is an involution: swap(swap(s)) == s for any state."""
    # Empty state
    emp = empty()
    assert swap(emp) == emp
    assert swap(swap(emp)) == emp

    # 1-term state without assertions
    s1 = DState(1, (0,), (0,))
    assert swap(s1) == s1
    assert swap(swap(s1)) == s1

    # Asymmetric 1-term state
    s_asym = DState(1, (1,), (0,))
    swapped = swap(s_asym)
    assert swapped == DState(1, (0,), (1,))
    assert swap(swapped) == s_asym

    # 2-term asymmetric state
    s2 = DState(2, (1, 0, 0, 0), (0, 1, 0, 0))
    assert swap(s2) == DState(2, (0, 1, 0, 0), (1, 0, 0, 0))
    assert swap(swap(s2)) == s2

    # Invariants preserved by swap
    assert s2.n == swap(s2).n
    assert s2.m == swap(s2).m
    assert s2.names == swap(s2).names


def test_change_model() -> None:
    """Change validation, properties, and written representations."""
    # Kinds
    assert len(KINDS) == 5
    assert Kind.SWAP in KINDS

    # Change creation and additions
    c_swap = Change(Kind.SWAP)
    assert c_swap.additions == (0, 0)
    assert not is_addition(c_swap)
    assert is_change(c_swap)

    c_term = Change(Kind.ADD_TERM)
    assert c_term.additions == (1, 0)
    assert is_addition(c_term)

    c_add = Change(Kind.ADD_ASSERTION, "r", 0, 0)
    assert c_add.additions == (0, 1)
    assert is_addition(c_add)

    c_rem = Change(Kind.REMOVE, "s", 0, 0)
    assert c_rem.additions == (0, 0)
    assert not is_addition(c_rem)

    c_id = Change(Kind.IDENTIFY, "", 0, 1)
    assert c_id.additions == (0, 0)
    assert not is_addition(c_id)

    # Written forms
    st = DState(2, (1, 0, 0, 0), (0, 1, 0, 0))
    assert c_swap.written(st) == "exchange the relations"
    assert c_term.written(st) == "add a term"
    assert c_add.written(st) == "add ara"
    assert c_rem.written(st) == "remove asa"
    assert c_id.written(st) == "identify a and b"

    # Validation errors
    with pytest.raises(ValueError, match="mentions relation 'r' or 's'"):
        Change(Kind.ADD_ASSERTION, "x", 0, 0)
    with pytest.raises(ValueError, match="mentions relation 'r' or 's'"):
        Change(Kind.REMOVE, "", 0, 0)
    with pytest.raises(ValueError, match="mention no relation"):
        Change(Kind.SWAP, "r")
    with pytest.raises(ValueError, match="mention no relation"):
        Change(Kind.ADD_TERM, "s")
    with pytest.raises(ValueError, match="mention no relation"):
        Change(Kind.IDENTIFY, "r", 0, 1)


def test_changes_ordering_and_readings() -> None:
    """Fewest additions first ordering; chosen vs unchosen readings."""
    emp = empty()
    # On empty state: under chosen reading, no swap because r == s
    ch_emp = changes(emp, allow_self_swap=False)
    assert len(ch_emp) == 1
    assert ch_emp[0].kind is Kind.ADD_TERM

    # Under unchosen reading: self-swap is present
    ch_emp_self = changes(emp, allow_self_swap=True)
    assert len(ch_emp_self) == 2
    assert ch_emp_self[0].kind is Kind.SWAP
    assert ch_emp_self[1].kind is Kind.ADD_TERM

    # On symmetric 1-term state (r == s == (0,))
    s_sym = DState(1, (0,), (0,))
    ch_sym = changes(s_sym, allow_self_swap=False)
    assert not any(c.kind is Kind.SWAP for c in ch_sym)

    ch_sym_self = changes(s_sym, allow_self_swap=True)
    assert any(c.kind is Kind.SWAP for c in ch_sym_self)

    # On asymmetric state: swap is present in chosen reading
    s_asym = DState(1, (1,), (0,))
    ch_asym = changes(s_asym, allow_self_swap=False)
    swap_changes = [c for c in ch_asym if c.kind is Kind.SWAP]
    assert len(swap_changes) == 1

    # Check fewest additions first: all (0,0) changes before additions
    saw_addition = False
    for c in ch_asym:
        if is_addition(c):
            saw_addition = True
        else:
            assert not saw_addition, f"non-addition {c} listed after addition"


def test_perform_and_loop_detection() -> None:
    """Outcome of changes and loop detection across relations."""
    s = DState(1, (1,), (0,))
    assert perform(s, Change(Kind.SWAP)) == DState(1, (0,), (1,))
    assert perform(s, Change(Kind.ADD_TERM)) == DState(2, (1, 0, 0, 0), (0, 0, 0, 0))
    assert perform(s, Change(Kind.REMOVE, "r", 0, 0)) == DState(1, (0,), (0,))
    assert perform(s, Change(Kind.ADD_ASSERTION, "s", 0, 0)) == DState(1, (1,), (1,))

    s2 = DState(2, (1, 0, 0, 0), (0, 0, 0, 0))
    assert perform(s2, Change(Kind.IDENTIFY, "", 0, 1)) == DState(1, (1,), (0,))

    # Loop detection: s has loop in r (0r0), none in s
    assert not s.legal_r
    assert s.legal_s
    # Swapping causes relation s to acquire the loop, and relation r becomes legal!
    assert makes_some_loop(s, Change(Kind.SWAP), "s")
    assert not makes_some_loop(s, Change(Kind.SWAP), "r")


def test_exploration_comparison_with_ninth() -> None:
    """Exploration from empty state matches Ninth exactly in depth, new_per_round, and sequence counts."""
    res = compare_with_ninth(bound=2, rounds=4)
    assert res["depth_identical"] is True
    assert res["new_per_round_identical"] is True
    assert res["sequence_counts_identical"] is True
    extra = res["extra_swap_attempts"]
    assert isinstance(extra, int) and extra > 0
    assert res["states_count"] == 36

    # Verify Exploration helper properties
    expl = explore(empty(), bound=2, rounds=4)
    assert expl.last_new_round == 4
    assert isinstance(expl.awaiting, list)
    assert isinstance(expl.frontier, list)

    # Validation errors on explore
    with pytest.raises(ValueError, match="state carries no names"):
        explore(DState(1, (0,), (0,), (0, 0)))
    with pytest.raises(ValueError, match="start exceeds bound"):
        explore(DState(3, (0,) * 9, (0,) * 9), bound=2)
    with pytest.raises(ValueError, match="bound admits at least one term"):
        explore(empty(), bound=0)
    with pytest.raises(ValueError, match="rounds is non-negative"):
        explore(empty(), bound=2, rounds=-1)

    # Explore with default args (start=None) and keep_log=True
    expl_default = explore(keep_log=True, bound=1, rounds=3)
    assert expl_default.start == empty()
    assert len(expl_default.log) > 0
    assert len(expl_default.new_per_round) == 4


def test_cost_reductions_and_formula() -> None:
    """Verify strictly shorter paths exist with swap and follow the exact reduction formula."""
    states = all_canonical_states(bound=2, max_m=2)
    assert len(states) == 32

    # Find cost reductions
    reductions = find_cost_reductions(states)
    assert len(reductions) == 220

    # Specifically check the 1-term asymmetric pair:
    s_r = DState(1, (1,), (0,))
    s_s = DState(1, (0,), (1,))
    matches = [r for r in reductions if r[0] == s_r and r[1] == s_s]
    assert len(matches) == 1
    src, tgt, d9, d10 = matches[0]
    assert d9 == 2  # remove 0r0, then add 0s0
    assert d10 == 1  # 1 swap!

    # Check larger reduction: 2 assertions swapped
    s_2r = DState(1, (2,), (0,))
    s_2s = DState(1, (0,), (2,))
    matches_2 = [r for r in reductions if r[0] == s_2r and r[1] == s_2s]
    assert len(matches_2) == 1
    _, _, d9_2, d10_2 = matches_2[0]
    assert d9_2 == 4  # remove 2 in r, add 2 in s
    assert d10_2 == 1  # 1 swap! Reduction of 3 steps!

    # Verify exact closed-form formula holds across all pairs
    assert verify_swap_reduction_formula(states) is True

    # Verify root-relative equality: from empty(), no cost reduction ever occurs!
    dist_9 = all_pairs_shortest_paths(states, include_swap=False)
    dist_10 = all_pairs_shortest_paths(states, include_swap=True)
    emp = empty()
    for tgt in states:
        assert dist_10[(emp, tgt)] == dist_9[(emp, tgt)]
        assert dist_10[(emp, tgt)] == tgt.n + tgt.m


def test_shortest_sequences_and_cycles() -> None:
    """Shortest sequence counting and 2-cycles."""
    expl = explore(empty(), bound=2, rounds=3)
    seqs = count_shortest_sequences(expl)
    assert seqs[empty()] == 1
    # 1-term bare state has 1 shortest sequence
    s1 = DState(1, (0,), (0,))
    assert seqs[s1] == 1

    # Transition graph cycles
    states = [DState(1, (1,), (0,)), DState(1, (0,), (1,))]
    g = transition_graph(states, include_swap=True)
    # Check that swap forms a 2-cycle
    assert any(ch.kind is Kind.SWAP and nxt == states[1] for ch, nxt in g[states[0]])
    assert any(ch.kind is Kind.SWAP and nxt == states[0] for ch, nxt in g[states[1]])


def test_attempt_and_exit() -> None:
    """Attempt with beyond bound."""
    s = DState(2, (0, 0, 0, 0), (0, 0, 0, 0))
    rec = attempt(s, Change(Kind.ADD_TERM), bound=2)
    assert rec.beyond is True
    assert rec.outcome is None

    rec_within = attempt(s, Change(Kind.SWAP), bound=2)
    assert rec_within.beyond is False
    assert rec_within.outcome is not None


def test_evidence_generation_and_check(tmp_path: Path) -> None:
    """Verify evidence generation and check mechanism."""
    # Test generation to a temporary directory
    ret_gen = evidence.main(["--out", str(tmp_path)])
    assert ret_gen == 0
    assert (tmp_path / "MANIFEST.sha256").exists()
    assert (tmp_path / "exploration_summary.json").exists()

    # Test check against the generated directory
    ret_check = evidence.main(["--check", "--out", str(tmp_path)])
    assert ret_check == 0

    # Test missing manifest check failure
    missing_dir = tmp_path / "missing"
    missing_dir.mkdir()
    ok_miss, msg_miss = evidence.verify_evidence(missing_dir)
    assert ok_miss is False
    assert "Manifest missing" in msg_miss

    # Test missing file check failure
    (tmp_path / "exploration_summary.json").unlink()
    ok_file, msg_file = evidence.verify_evidence(tmp_path)
    assert ok_file is False
    assert "missing" in msg_file

    # Test byte mismatch check failure
    p_bad = tmp_path / "exploration_summary.json"
    p_bad.write_text("corrupted content", encoding="utf-8")
    ok_bad, msg_bad = evidence.verify_evidence(tmp_path)
    assert ok_bad is False
    assert "Byte mismatch" in msg_bad

