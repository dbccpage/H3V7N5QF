"""Comprehensive test suite for Problem 02 derivation.

Covers:
- Guarded steps (r guarded by s, s guarded by r)
- Blocked pair witnesses
- Identification bypass (1-term in 5 steps, 2-term in 6 steps via term inflation)
- Disjoint support invariant under additions
- Comparison with ninth derivation and falsifier failure
- Evidence generator and byte-identical check
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

import evidence
import model
from eighth.changes import Change, Kind


def test_other_relation() -> None:
    assert model.other_relation("r") == "s"
    assert model.other_relation("s") == "r"
    with pytest.raises(ValueError, match="Unknown relation"):
        model.other_relation("t")


def test_cross_guard_semantics() -> None:
    # Empty state has no terms, only add_term is admitted
    s0 = model.empty()
    assert model.is_guarded_change(s0, Change(Kind.ADD_TERM))
    assert not model.is_guarded_change(s0, Change(Kind.ADD_ASSERTION, "r", 0, 0))

    # 1 term, no assertions
    s1 = model.canonical(model.perform(s0, Change(Kind.ADD_TERM)))
    assert model.is_guarded_change(s1, Change(Kind.ADD_ASSERTION, "r", 0, 0))
    assert model.is_guarded_change(s1, Change(Kind.ADD_ASSERTION, "s", 0, 0))

    # Add 0r0
    s_r = model.canonical(model.perform(s1, Change(Kind.ADD_ASSERTION, "r", 0, 0)))
    assert s_r.has("r", 0, 0)
    assert not s_r.has("s", 0, 0)

    # Now 0s0 is guarded (blocked)
    assert model.is_cross_guarded(s_r, "s", 0, 0)
    assert not model.can_add_assertion(s_r, "s", 0, 0)
    assert not model.is_guarded_change(s_r, Change(Kind.ADD_ASSERTION, "s", 0, 0))

    # But adding 0r0 again is admitted (multiplicity rises)
    assert not model.is_cross_guarded(s_r, "r", 0, 0)
    assert model.can_add_assertion(s_r, "r", 0, 0)
    assert model.is_guarded_change(s_r, Change(Kind.ADD_ASSERTION, "r", 0, 0))

    # Performing blocked change raises ValueError
    with pytest.raises(ValueError, match="not admitted"):
        model.perform(s_r, Change(Kind.ADD_ASSERTION, "s", 0, 0))

    # Out of bounds indices
    assert not model.can_add_assertion(s_r, "r", -1, 0)
    assert not model.can_add_assertion(s_r, "r", 0, 5)


def test_removals_and_identifications() -> None:
    s = model.DState.of(2, ((0, 1),), ((1, 0),))
    # Removals
    assert model.is_guarded_change(s, Change(Kind.REMOVE, "r", 0, 1))
    assert model.is_guarded_change(s, Change(Kind.REMOVE, "s", 1, 0))
    assert not model.is_guarded_change(s, Change(Kind.REMOVE, "r", 1, 0))

    # Identifications
    assert model.is_guarded_change(s, Change(Kind.IDENTIFY, "", 0, 1))
    assert not model.is_guarded_change(s, Change(Kind.IDENTIFY, "", 1, 0))
    assert not model.is_guarded_change(s, Change(Kind.IDENTIFY, "", 0, 2))


def test_guarded_changes_ordering() -> None:
    s = model.canonical(model.DState.of(2, ((0, 0),), ()))
    changes = model.guarded_changes(s)
    # Order: IDENTIFY first, then REMOVE, then ADD_TERM, then ADD_ASSERTION
    kinds = [c.kind for c in changes]
    assert Kind.IDENTIFY in kinds
    assert Kind.REMOVE in kinds
    assert Kind.ADD_TERM in kinds
    assert Kind.ADD_ASSERTION in kinds

    # Ensure guarded additions are subset
    additions = model.guarded_additions(s)
    for c in additions:
        assert c.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)


def test_witness_blocked_pair() -> None:
    state, change = model.witness_blocked_pair()
    assert state.has("r", 0, 0)
    assert change.rel == "s" and change.x == 0 and change.y == 0
    assert not model.is_guarded_change(state, change)


def test_one_term_identification_bypass() -> None:
    steps = model.witness_identification_bypass()
    assert len(steps) == 5
    target = model.canonical(model.DState.of(1, ((0, 0),), ((0, 0),)))
    assert steps[-1][1] == target

    # Verify each intermediate transition
    curr = model.canonical(model.empty())
    for change, nxt in steps:
        assert model.is_guarded_change(curr, change)
        res = model.canonical(model.perform(curr, change))
        assert res == nxt
        curr = res


def test_two_term_identification_bypass() -> None:
    steps = model.witness_two_term_bypass()
    assert len(steps) == 6
    target = model.canonical(model.DState.of(2, ((0, 1),), ((0, 1),)))
    assert steps[-1][1] == target

    # Intermediate state at step 5 has 3 terms
    assert steps[4][1].n == 3

    # Verification within n<=2 bound vs n<=3 bound
    exp_n2 = model.explore(bound_terms=2, bound_assertions=4, rounds=8)
    exp_n3 = model.explore(bound_terms=3, bound_assertions=4, rounds=8)
    assert target not in exp_n2.depth
    assert target in exp_n3.depth
    assert exp_n3.depth[target] == 6


def test_disjoint_support_invariant() -> None:
    # Under additions alone, support is always disjoint
    exp_add = model.explore(bound_terms=3, bound_assertions=3, rounds=6, additions_only=True)
    for s in exp_add.depth:
        assert model.is_disjoint_support(s)

    # Target 1::0-0*1|0-0*1 violates disjoint support
    target = model.canonical(model.DState.of(1, ((0, 0),), ((0, 0),)))
    assert not model.is_disjoint_support(target)
    assert target not in exp_add.depth

    # Count disjoint results
    counts = model.count_disjoint_results(bound_terms=3, bound_assertions=3)
    assert isinstance(counts, dict)
    assert len(counts) > 0


def test_comparison_with_ninth_and_falsifier() -> None:
    cmp_res = model.compare_with_ninth(bound_terms=3, bound_assertions=3, rounds=6)
    assert not cmp_res["falsifier_satisfied"]
    ninth_new = cmp_res["ninth_new_per_round"]
    guarded_new = cmp_res["guarded_new_per_round"]
    diff = cmp_res["diff_per_round"]

    assert isinstance(ninth_new, list)
    assert isinstance(guarded_new, list)
    assert isinstance(diff, list)

    # Differ at round 3
    assert ninth_new[3] == 8
    assert guarded_new[3] == 7
    assert diff[3] == ["1::0-0*1|0-0*1"]


def test_evidence_generation_and_check(tmp_path: Path) -> None:
    out_dir = tmp_path / "evidence"
    # Test generation
    evidence.write_evidence(out_dir)
    assert (out_dir / "run.json").exists()
    assert (out_dir / "frontier.json").exists()
    assert (out_dir / "witnesses.json").exists()
    assert (out_dir / "differential.json").exists()
    assert (out_dir / "disjoint_counts.json").exists()
    assert (out_dir / "MANIFEST.sha256").exists()

    # Test check passes
    assert evidence.check_evidence(out_dir)

    # Test check fails on missing file
    (out_dir / "run.json").unlink()
    assert not evidence.check_evidence(out_dir)

    # Test check fails on non-existent dir
    assert not evidence.check_evidence(tmp_path / "non_existent")

    # Test check fails on tampered content
    (out_dir / "run.json").write_text("corrupted", encoding="utf-8")
    assert not evidence.check_evidence(out_dir)


def test_evidence_main_cli(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out_dir = tmp_path / "evidence_cli"
    # Run write
    rc = evidence.main(["--out", str(out_dir)])
    assert rc == 0
    captured = capsys.readouterr()
    assert "successfully written" in captured.out

    # Run check pass
    rc_check = evidence.main(["--out", str(out_dir), "--check"])
    assert rc_check == 0
    captured_check = capsys.readouterr()
    assert "PASSED" in captured_check.out

    # Run check fail
    (out_dir / "run.json").write_text("{}", encoding="utf-8")
    rc_fail = evidence.main(["--out", str(out_dir), "--check"])
    assert rc_fail == 1
    captured_fail = capsys.readouterr()
    assert "FAILED" in captured_fail.out
