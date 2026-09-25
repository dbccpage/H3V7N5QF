"""Comprehensive test suite for Problem 04 (Written Refusal) derivation.

Verifies:
1. Written identity, properties, and orbit-stabilizer theorem.
2. Refusal semantics: loop detection, state invariance, and accounting.
3. Breadth-first exploration at bound 3 under all 4 combinations (bra x sameness).
4. Strict equality of written refusal closure with Eighteenth closure at every round (Falsifier holds).
5. Projection of written refusal closure onto Twentyfirst canonical quotient closure.
6. Non-trivial fiber splitting: quotient classes containing multiple written representatives.
7. Independent census by relation counting and orbit partition.
8. Evidence generation and `--check` CLI functionality, including mismatch detection.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import cast

import pytest

# Ensure derivation directory is on sys.path
HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

# Ensure repo code/ directory is on sys.path
ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:
    sys.path.insert(0, str(ROOT / "code"))

from evidence import main as evidence_main, measure_run, write_all  # noqa: E402
from model import (  # noqa: E402
    AttemptRecord,
    WrittenRefusalExploration,
    aut_size,
    compare_with_eighteenth,
    compare_with_twentyfirst,
    explore_written_refusal,
    independent_written_census,
    orbit,
    orbit_size,
    orbit_splits_factorial,
    refusal_result,
    refused,
    same_written,
    to_quotient,
    total_census_count,
    verify_census,
)
from xry.state import Sameness, State, canonical, given, rewrite  # noqa: E402


def test_written_identity_and_quotient() -> None:
    """Distinct writings of identical structure are different written states but identical in quotient."""
    s1 = State.of(2, [(0, 1)], names=None)
    s2 = State.of(2, [(1, 0)], names=None)

    assert not same_written(s1, s2)
    assert s1 != s2
    assert s1.key() != s2.key()

    # In canonical quotient, they are identified
    assert to_quotient(s1) == to_quotient(s2)
    assert canonical(s1) == canonical(s2)

    # Identical state is same written
    assert same_written(s1, State.of(2, [(0, 1)], names=None))


def test_orbit_and_stabilizer() -> None:
    """Orbit size times automorphism size equals n! for all written states."""
    # Empty graph on 3 terms: orbit size 1, Aut size 6
    s_empty = State.of(3, [], names=None)
    assert orbit_size(s_empty) == 1
    assert aut_size(s_empty) == 6
    assert orbit_splits_factorial(s_empty)
    assert orbit(s_empty) == frozenset([s_empty])

    # Single directed edge on 3 terms: 6 possible directed edges, Aut size 1
    s_edge = State.of(3, [(0, 1)], names=None)
    assert orbit_size(s_edge) == 6
    assert aut_size(s_edge) == 1
    assert orbit_splits_factorial(s_edge)

    # State with names (anchored): orbit size under name-preserving or name-moving permutations
    s_named = State.of(2, [(0, 1)], names=(0, 1))
    assert orbit_size(s_named) == 2
    assert aut_size(s_named) == 1
    assert orbit_splits_factorial(s_named)


def test_refusal_logic() -> None:
    """Obstructed changes produce loop assertions, are refused, and change nothing."""
    legal_state = State.of(2, [(0, 1)], names=(0, 1))
    illegal_state = State.of(2, [(0, 0)], names=(0, 1))

    assert not refused(legal_state)
    assert refused(illegal_state)

    # Refusal changes nothing: returns the exact same state
    assert refusal_result(legal_state) is legal_state
    assert refusal_result(illegal_state) is illegal_state


def test_exploration_validation() -> None:
    """Exploration enforces valid start state and bound constraints."""
    illegal_start = State.of(2, [(0, 0)], names=(0, 1))
    with pytest.raises(ValueError, match="what is given asserts no xrx"):
        explore_written_refusal(illegal_start, bound=3)

    legal_start = State.of(3, [(0, 1)], names=None)
    with pytest.raises(ValueError, match="the bound is below what is given"):
        explore_written_refusal(legal_start, bound=2)


def test_exploration_free_closure() -> None:
    """FREE exploration reaches 69 states at bound 3, with exact round waves matching Eighteenth."""
    start = given(False, Sameness.FREE)
    expl = explore_written_refusal(start, bound=3, rounds=12, keep_log=True)

    assert len(expl.depth) == 69
    assert expl.new_per_round == [1, 3, 8, 15, 20, 15, 6, 1, 0, 0, 0, 0, 0]
    assert expl.total_refusals > 0
    assert len(expl.frontier) == 64
    assert len(expl.log) > 0

    # Every logged record has expected attributes
    rec = expl.log[0]
    assert isinstance(rec, AttemptRecord)
    assert isinstance(rec.obstructed, bool)

    # Test census match
    assert verify_census(expl, Sameness.FREE)


def test_exploration_anchored_closure() -> None:
    """ANCHORED exploration reaches 137 states at bound 3, with exact round waves matching Eighteenth."""
    start = given(False, Sameness.ANCHORED)
    expl = explore_written_refusal(start, bound=3, rounds=12, keep_log=False)

    assert len(expl.depth) == 137
    assert expl.new_per_round == [1, 3, 8, 16, 23, 22, 21, 21, 15, 6, 1, 0, 0]
    assert len(expl.frontier) == 128
    assert verify_census(expl, Sameness.ANCHORED)


def test_independent_census_formulas() -> None:
    """Independent census matches closed form 2^(n*(n-1)) for FREE and anchored multipliers."""
    census_free = independent_written_census(3, Sameness.FREE)
    assert census_free == {1: 1, 2: 4, 3: 64}
    assert total_census_count(3, Sameness.FREE) == 69

    census_anchored = independent_written_census(3, Sameness.ANCHORED)
    assert census_anchored == {1: 1, 2: 8, 3: 128}
    assert total_census_count(3, Sameness.ANCHORED) == 137


def test_falsifier_exact_match_with_eighteenth() -> None:
    """The written refusal closure is exactly the Eighteenth closure at every round across all 4 configs."""
    for bra in (False, True):
        for sameness in (Sameness.ANCHORED, Sameness.FREE):
            comp = compare_with_eighteenth(bra, sameness, bound=3, rounds=12)
            assert comp["depth_matches"], f"Depth mismatch for bra={bra}, sameness={sameness}"
            assert comp["waves_match"], f"Waves mismatch for bra={bra}, sameness={sameness}"
            assert comp["frontier_matches"], f"Frontier mismatch for bra={bra}, sameness={sameness}"
            assert len(comp["disagreements"]) == 0  # type: ignore[arg-type]
            assert len(comp["round_mismatches"]) == 0  # type: ignore[arg-type]


def test_twentyfirst_quotient_projection_and_fiber_splitting() -> None:
    """Projecting the written refusal closure by canonical renaming yields Twentyfirst's quotient closure."""
    for bra in (False, True):
        for sameness in (Sameness.ANCHORED, Sameness.FREE):
            comp = compare_with_twentyfirst(bra, sameness, bound=3, rounds=12)
            assert comp["quotient_matches"]
            assert cast(int, comp["splitting_classes_count"]) > 0
            assert cast(int, comp["max_fiber_size"]) > 1

    # Check specific fiber counts for FREE
    comp_free = compare_with_twentyfirst(False, Sameness.FREE, bound=3, rounds=12)
    assert comp_free["twentyfirst_count"] == 20
    assert comp_free["written_count"] == 69
    assert comp_free["splitting_classes_count"] == 15
    assert comp_free["max_fiber_size"] == 6  # 3! = 6 distinct writings for an asymmetric graph on 3 terms


def test_measure_run_and_evidence_generation(tmp_path: Path) -> None:
    """Measure run gathers full metrics and write_all outputs valid JSON summary and manifest."""
    res = measure_run(False, Sameness.FREE, bound=3, rounds=12)
    assert res["written_results"] == 69
    assert res["eighteenth_depth_matches"] is True
    assert res["twentyfirst_quotient_matches"] is True
    assert res["census_matches"] is True
    assert len(res["orbit_formula_fails"]) == 0  # type: ignore[arg-type]

    out_dir = tmp_path / "evidence"
    summary = write_all(out_dir, bound=3, rounds=12)
    assert summary["falsifier_holds"] is True
    assert summary["hypothesis_holds"] is False
    assert (out_dir / "summary.json").is_file()
    assert (out_dir / "MANIFEST.sha256").is_file()


def test_evidence_cli_and_check(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Evidence CLI correctly writes, verifies with --check, and detects errors."""
    ev_dir = tmp_path / "ev_cli"

    # 1. Missing directory with --check returns 1
    code = evidence_main(["--out", str(ev_dir), "--check"])
    assert code == 1

    # 2. Normal generation writes files and returns 0
    code = evidence_main(["--out", str(ev_dir), "--bound", "2", "--rounds", "4"])
    assert code == 0
    assert (ev_dir / "summary.json").is_file()

    # 3. Successful --check returns 0
    code = evidence_main(["--out", str(ev_dir), "--bound", "2", "--rounds", "4", "--check"])
    assert code == 0

    # 4. Tampered directory with --check detects discrepancy and returns 1
    (ev_dir / "summary.json").write_text("tampered content\n", encoding="utf-8")
    code = evidence_main(["--out", str(ev_dir), "--bound", "2", "--rounds", "4", "--check"])
    assert code == 1
