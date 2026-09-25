"""Comprehensive Pytest test suite for Problem 01 (Remove Bare Term).

Tests state and step semantics, the two-step cycle, orbit counts,
differential checks, and mutation checks to ensure >= 95% branch coverage.
"""

from __future__ import annotations

from enum import IntEnum
from pathlib import Path

import pytest
from model import (
    AttemptRecord,
    Change,
    Exit,
    Exploration,
    Kind,
    State,
    _conjugacy_class_size,
    _count_fixed_configurations,
    _integer_partitions,
    _pair_cycle_lengths,
    attempt,
    attempt_counts,
    burnside_orbits,
    canonical_orbits_count,
    changes,
    cost,
    empty,
    explore,
    is_bare,
    perform,
    reachable,
    two_step_cycle,
    two_term_count,
)


# --- 1. State Model Tests ---


def test_state_basic_and_validation() -> None:
    s0 = empty()
    assert s0.n == 0
    assert s0.m == 0
    assert s0.size == 0
    assert s0.distinct == 0
    assert s0.pairs == ()
    assert s0.bare_terms == ()
    assert s0.canonical() == s0

    # Validation errors
    with pytest.raises(ValueError, match="number of terms cannot be negative"):
        State(-1, ())
    with pytest.raises(ValueError, match="does not match n\\*n"):
        State(2, (0, 0, 0))
    with pytest.raises(ValueError, match="multiplicities cannot be negative"):
        State(1, (-1,))
    with pytest.raises(ValueError, match="term out of range"):
        s0.mult_of(0, 0)
    with pytest.raises(ValueError, match="term 2 not in 0..1"):
        State(2, (0, 0, 0, 0)).is_bare(2)


def test_state_canonical_and_bare() -> None:
    # 1-term state
    s1 = State(1, (3,))
    assert s1.canonical() == s1
    assert not s1.is_bare(0)
    assert s1.bare_terms == ()
    assert s1.pairs == ((0, 0),)

    s1_bare = State(1, (0,))
    assert s1_bare.is_bare(0)
    assert s1_bare.bare_terms == (0,)
    assert is_bare(s1_bare, 0)

    # 2-term state with bare term
    # 0 -> 0 (loop), 1 is isolated
    s2 = State(2, (1, 0, 0, 0))
    assert not s2.is_bare(0)
    assert s2.is_bare(1)
    assert s2.bare_terms == (1,)

    # 2-term state canonical form:
    # Between (1, 0, 0, 0) and (0, 0, 0, 1), (0, 0, 0, 1) is lexicographically smaller
    assert s2.canonical() == State(2, (0, 0, 0, 1))
    s2_non_can = State(2, (0, 0, 0, 1))
    assert s2_non_can.canonical() == State(2, (0, 0, 0, 1))


# --- 2. Kind and Change Tests ---


def test_kind_written() -> None:
    assert Kind.IDENTIFY.written() == "identify two terms"
    assert Kind.REMOVE.written() == "remove an assertion"
    assert Kind.ADD_TERM.written() == "add a term"
    assert Kind.ADD_ASSERTION.written() == "add an assertion"
    assert Kind.REMOVE_BARE_TERM.written() == "remove a term that names no assertion"


def test_change_validation_and_methods() -> None:
    # Valid changes
    c_id = Change(Kind.IDENTIFY, 0, 1)
    assert c_id.additions == (0, 0)
    assert not c_id.is_addition
    assert c_id.written() == "identify 0 and 1"

    c_rem = Change(Kind.REMOVE, 1, 2)
    assert c_rem.additions == (0, 0)
    assert not c_rem.is_addition
    assert c_rem.written() == "remove 1r2"

    c_add_t = Change(Kind.ADD_TERM)
    assert c_add_t.additions == (1, 0)
    assert c_add_t.is_addition
    assert c_add_t.written() == "add a term"

    c_add_a = Change(Kind.ADD_ASSERTION, 0, 1)
    assert c_add_a.additions == (0, 1)
    assert c_add_a.is_addition
    assert c_add_a.written() == "add 0r1"

    c_bare = Change(Kind.REMOVE_BARE_TERM, 2)
    assert c_bare.additions == (0, 0)
    assert not c_bare.is_addition
    assert c_bare.written() == "remove bare term 2"

    # Validation errors
    with pytest.raises(ValueError, match="IDENTIFY requires 0 <= x < y"):
        Change(Kind.IDENTIFY, 1, 0)
    with pytest.raises(ValueError, match="IDENTIFY requires 0 <= x < y"):
        Change(Kind.IDENTIFY, -1, 1)
    with pytest.raises(ValueError, match="REMOVE requires non-negative terms"):
        Change(Kind.REMOVE, -1, 0)
    with pytest.raises(ValueError, match="ADD_TERM takes no terms"):
        Change(Kind.ADD_TERM, 0, -1)
    with pytest.raises(ValueError, match="ADD_ASSERTION requires non-negative terms"):
        Change(Kind.ADD_ASSERTION, 0, -1)
    with pytest.raises(ValueError, match="REMOVE_BARE_TERM requires non-negative term"):
        Change(Kind.REMOVE_BARE_TERM, -1, -1)
    with pytest.raises(ValueError, match="REMOVE_BARE_TERM requires non-negative term"):
        Change(Kind.REMOVE_BARE_TERM, 0, 1)


# --- 3. Step Semantics and Actions ---


def test_perform_and_changes() -> None:
    s0 = empty()
    ch0 = changes(s0)
    assert len(ch0) == 1
    assert ch0[0].kind == Kind.ADD_TERM
    assert attempt_counts(s0) == (1, 1)

    # Perform add term on empty
    s1 = perform(s0, ch0[0])
    assert s1 == State(1, (0,))
    assert s1.n == 1
    assert s1.m == 0

    # Changes on s1 (1 term, 0 assertions)
    ch1 = changes(s1)
    # Expected:
    # 0 additions: REMOVE_BARE_TERM(0) (1 change)
    # 1 addition: ADD_TERM, ADD_ASSERTION(0, 0) (2 changes)
    assert len(ch1) == 3
    assert ch1[0] == Change(Kind.REMOVE_BARE_TERM, 0)
    assert ch1[1] == Change(Kind.ADD_TERM)
    assert ch1[2] == Change(Kind.ADD_ASSERTION, 0, 0)
    assert attempt_counts(s1) == (3, 2)

    # Perform bare-term removal on s1 -> reaches empty!
    s0_back = perform(s1, ch1[0])
    assert s0_back == empty()

    # Perform add assertion on s1
    s1_loop = perform(s1, ch1[2])
    assert s1_loop == State(1, (1,))
    assert s1_loop.pairs == ((0, 0),)

    # Perform remove assertion on s1_loop
    c_rem_a = Change(Kind.REMOVE, 0, 0)
    assert perform(s1_loop, c_rem_a) == s1

    # Error removing unasserted
    with pytest.raises(ValueError, match="cannot remove non-asserted pair"):
        perform(s1, c_rem_a)

    # Error removing non-bare term
    with pytest.raises(ValueError, match="names an assertion and cannot be removed as bare"):
        perform(s1_loop, Change(Kind.REMOVE_BARE_TERM, 0))

    # Error for unknown change kind
    class FakeKind(IntEnum):
        UNKNOWN = 99
    bad_change = Change.__new__(Change)
    object.__setattr__(bad_change, "kind", FakeKind.UNKNOWN)
    with pytest.raises(ValueError, match="unknown kind"):
        perform(s1, bad_change)


def test_perform_identify_and_bare_term_multi() -> None:
    # State with 3 terms:
    # 0 -> 1 with multiplicity 2
    # term 2 is bare
    # mult matrix (3x3):
    # (0, 2, 0,
    #  0, 0, 0,
    #  0, 0, 0)
    mult = (0, 2, 0, 0, 0, 0, 0, 0, 0)
    s3 = State(3, mult)
    assert s3.is_bare(2)
    assert not s3.is_bare(0)
    assert not s3.is_bare(1)

    # Remove bare term 2
    s2 = perform(s3, Change(Kind.REMOVE_BARE_TERM, 2))
    assert s2.n == 2
    assert s2.mult == (0, 2, 0, 0)
    assert s2.m == 2

    # Remove bare term at index 0 when term 0 is bare:
    # terms: 0 (bare), 1 -> 2 (mult 1)
    # mult matrix:
    # (0, 0, 0,
    #  0, 0, 1,
    #  0, 0, 0)
    s3_b0 = State(3, (0, 0, 0, 0, 0, 1, 0, 0, 0))
    assert s3_b0.is_bare(0)
    s2_b0 = perform(s3_b0, Change(Kind.REMOVE_BARE_TERM, 0))
    assert s2_b0.n == 2
    # Old terms 1, 2 become 0, 1: pair (0, 1) has multiplicity 1
    assert s2_b0.mult == (0, 1, 0, 0)
    assert s2_b0.m == 1

    # Identification: identify 0 and 1 in s2 (which has 0->1 with mult 2)
    # Merging 0 and 1 turns 0->1 into 0->0 with mult 2
    s1_id = perform(s2, Change(Kind.IDENTIFY, 0, 1))
    assert s1_id.n == 1
    assert s1_id.mult == (2,)


# --- 4. Two-Step Cycle and Falsifier Tests ---


def test_two_step_cycle_verification() -> None:
    s0, c1, s1, c2, s2 = two_step_cycle()
    assert s0 == empty()
    assert c1 == Change(Kind.ADD_TERM)
    assert s1 == State(1, (0,))
    assert c2 == Change(Kind.REMOVE_BARE_TERM, 0)
    assert s2 == empty()

    # Hypothesis: bare-term removal destroys one-way reachability of empty
    # Empty in-degree > 0
    incoming_changes = [c for c in changes(s1) if perform(s1, c).canonical() == empty()]
    assert len(incoming_changes) == 1
    assert incoming_changes[0] == Change(Kind.REMOVE_BARE_TERM, 0)

    # Falsifier: "No nonempty result reaches the empty beginning within two changes."
    # We witness s1 (nonempty, n=1) reaching empty in exactly 1 change (<= 2).
    # Thus the falsifier condition is refuted / falsified.
    assert s1.n > 0
    assert perform(s1, c2).canonical() == empty()


# --- 5. Exploration and Frontier Tests ---


def test_explore_basic_and_frontier() -> None:
    with pytest.raises(ValueError, match="start has more terms than bound"):
        explore(start=State(3, (0,) * 9), bound=2)

    expl = explore(start=empty(), bound=2, rounds=4, keep_log=True)
    # Expected waves:
    # round 0: empty (size 0) -> 1
    # round 1: (1, 0) (size 1) -> 1
    # round 2: (2, 0), (1, 1) (size 2) -> 2
    # round 3: (2, 1) [2 states], (1, 2) [1 state] (size 3) -> 3
    # round 4: (2, 2) [6 states], (1, 3) [1 state] (size 4) -> 7
    assert expl.new_per_round[:5] == [1, 1, 2, 3, 7]
    assert expl.total_discovered == 1 + 1 + 2 + 3 + 7  # 14 states

    # Frontier exits
    # Any attempt to add term to a 2-term state exits bound 2
    assert len(expl.frontier) > 0
    for exit_rec in expl.frontier:
        assert isinstance(exit_rec, Exit)
        assert exit_rec.change.kind == Kind.ADD_TERM
        assert exit_rec.source.n == 2

    # Log checks
    assert len(expl.log) > 0
    sample_rec = expl.log[0]
    assert isinstance(sample_rec, AttemptRecord)
    assert sample_rec.disposition == "valid"


def test_reachability_and_cost() -> None:
    s0 = empty()
    s1 = State(1, (2,))
    s2 = State(2, (1, 0, 1, 0))

    assert cost(s0) == 0
    assert cost(s1) == 3
    assert cost(s2) == 4

    assert reachable(s0, s1)
    assert reachable(s1, s0)
    assert reachable(s1, s2)
    assert reachable(s2, s1)


# --- 6. Combinatorial Burnside Orbit Tests ---


def test_two_term_count() -> None:
    with pytest.raises(ValueError, match="multiplicity cannot be negative"):
        two_term_count(-1)

    # Closed form:
    # m = 0: (C(3,3) + 1)/2 = 1
    # m = 1: (C(4,3) + 0)/2 = 2
    # m = 2: (C(5,3) + 2)/2 = (10 + 2)/2 = 6
    # m = 3: (C(6,3) + 0)/2 = 20/2 = 10
    # m = 4: (C(7,3) + 3)/2 = (35 + 3)/2 = 19
    expected = [1, 2, 6, 10, 19]
    actual = [two_term_count(m) for m in range(5)]
    assert actual == expected


def test_burnside_helpers_and_orbits() -> None:
    # Integer partitions
    assert _integer_partitions(0) == [[]]
    assert _integer_partitions(1) == [[1]]
    assert _integer_partitions(2) == [[2], [1, 1]]
    assert len(_integer_partitions(4)) == 5

    # Conjugacy classes
    assert _conjugacy_class_size(2, [2]) == 1
    assert _conjugacy_class_size(2, [1, 1]) == 1

    # Pair cycle lengths
    assert sorted(_pair_cycle_lengths([2])) == [2, 2]
    assert sorted(_pair_cycle_lengths([1, 1])) == [1, 1, 1, 1]

    # Fixed configurations
    assert _count_fixed_configurations([1, 1, 1, 1], 2) == 10

    # Burnside orbits
    assert burnside_orbits(0, 0) == 1
    assert burnside_orbits(0, 1) == 0
    assert canonical_orbits_count(0, 0) == 1
    assert canonical_orbits_count(0, 1) == 0
    assert canonical_orbits_count(1, 0) == 1
    assert canonical_orbits_count(1, 4) == 1

    for m in range(6):
        assert canonical_orbits_count(2, m) == two_term_count(m)
        assert burnside_orbits(2, m) == two_term_count(m)


# --- 7. Differential Checks ---


def test_differential_bfs_vs_orbits() -> None:
    # Explore with bound = 2, rounds = 5
    expl = explore(bound=2, rounds=5)

    # For each round r from 0 to 5, all discovered states must have size == r
    for r, wave in enumerate(expl.waves):
        for s in wave:
            assert s.size == r
            assert cost(s) == r

    # Count of results of round r with at most 2 terms:
    # r = 0: n=0, m=0 -> 1
    # r = 1: n=1, m=0 -> 1
    # r >= 2: n=1, m=r-1 (1 state) + n=2, m=r-2 (two_term_count(r-2) states)
    for r in range(6):
        expected_count = 1 if r in (0, 1) else (1 + two_term_count(r - 2))
        assert len(expl.waves[r]) == expected_count


# --- 8. Mutation Checks ---


def test_mutation_forbidding_bare_term_removal_restores_one_way_reachability() -> None:
    """Mutation check: If Kind.REMOVE_BARE_TERM is omitted, empty has in-degree 0."""
    s1 = State(1, (0,))
    changes_without_bare = [c for c in changes(s1) if c.kind != Kind.REMOVE_BARE_TERM]
    outcomes = [perform(s1, c).canonical() for c in changes_without_bare]
    assert empty() not in outcomes
    assert all(out.n >= 1 for out in outcomes)


def test_mutation_illegal_bare_term_removal_fails() -> None:
    """Mutation check: Attempting bare term removal on an asserted term raises."""
    s1_asserted = State(1, (1,))
    with pytest.raises(ValueError):
        perform(s1_asserted, Change(Kind.REMOVE_BARE_TERM, 0))


# --- 9. Evidence Generation and Verification Tests ---


def test_evidence_generation_and_check(tmp_path: Path) -> None:
    import evidence
    from evidence import generate_all, main, verify_check

    # Generate in temp dir
    files = generate_all(tmp_path)
    assert "frontier.txt" in files
    assert "waves.json" in files
    assert "cycle_witness.json" in files
    assert "resolution.json" in files
    assert "differential_checks.json" in files
    assert "MANIFEST.sha256" in files

    # Verification passes
    assert verify_check(tmp_path)

    # Verification fails if directory missing
    non_existent = tmp_path / "non_existent"
    assert not verify_check(non_existent)

    # Verification fails if a file is tampered
    tampered_file = tmp_path / "resolution.json"
    tampered_file.write_text("corrupted content", encoding="utf-8")
    assert not verify_check(tmp_path)

    # Verification fails if a file is extra or missing
    tampered_file.unlink()
    assert not verify_check(tmp_path)


def test_evidence_cli(tmp_path: Path) -> None:
    import evidence
    from evidence import main

    out_dir = tmp_path / "evidence_cli"
    # Run main to generate
    rc_gen = main(["--out", str(out_dir)])
    assert rc_gen == 0

    # Run main with --check
    rc_check = main(["--check", "--out", str(out_dir)])
    assert rc_check == 0

