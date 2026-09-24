"""Tests for Problem 09 (Two-Step Leftover) Derivation.

Covers:
- LeftOver enum values matching seed prompt wording
- Addition leftover behavior (always NOTHING_LEFT)
- Removal leftover behavior (always CLEARABLE in 1 and 2 steps)
- Identification leftover behavior:
  - Bare-term identification (CLEARABLE in 1 and 2 steps)
  - Non-bare-term identification (UNCLEARED in 1 and 2 steps, CLEARABLE in 3 steps)
- Size Parity Invariant: odd required delta impossible in even number of steps
- Comparison across explored states and edge cases
- Falsifier confirmation and hypothesis refutation
"""

from __future__ import annotations

import json
import runpy
import sys
from pathlib import Path

import pytest

# Ensure paths
_HERE = Path(__file__).resolve().parent
_REPO_ROOT = _HERE.parents[3]
_CODE_DIR = _REPO_ROOT / "code"
if str(_CODE_DIR) not in sys.path:
    sys.path.insert(0, str(_CODE_DIR))
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

from ninth.changes import Change, Kind  # noqa: E402
from ninth.state import DState, empty  # noqa: E402
from tenth.invariants import bare  # noqa: E402

from model import (  # noqa: E402
    LeftOver,
    clearing_sequence_one,
    clearing_sequence_three,
    clearing_sequence_two,
    compare_all_leftovers,
    generate_edge_case_states,
    independent_classification_census,
    leftover_of_one_step,
    leftover_of_two_step,
    parity_analysis,
    restores_in_k_steps,
    three_step_restoration_witness,
    verify_falsifier,
)
import evidence  # noqa: E402
from evidence import (  # noqa: E402
    build_evidence,
    compare_files,
    write_evidence,
)


def test_leftover_enum_values() -> None:
    """Check enum values match seed prompt verbatim."""
    assert LeftOver.NOTHING_LEFT.value == "nothing left"
    assert (
        LeftOver.CLEARABLE.value
        == "a leftover that a sequence of at most two later changes of the four kinds can clear"
    )
    assert LeftOver.UNCLEARED.value == "a leftover that no such sequence can clear"
    assert str(LeftOver.NOTHING_LEFT) == "nothing left"


def test_restores_in_k_steps_base_cases() -> None:
    """Test boundary conditions for k = 0, 1, 2."""
    s = DState(1, (0,), (0,), names=None)
    c_add = Change(Kind.ADD_TERM, "", 1, 0)
    # k = 0: out has 2 terms, start has 1 term, cannot be same
    res0 = restores_in_k_steps(s, c_add, max_k=0)
    assert not res0.restored
    assert res0.length == 0
    assert res0.sequence == ()

    # If out were same as state:
    # A removal on state with 0 assertions is not legal, but let's test a state where out is identical to state
    # (e.g. dummy test of same(out, state))
    s_zero = empty()
    # Adding a term gives 1 term
    c1 = Change(Kind.ADD_TERM, "", 0, 0)
    res_k1 = restores_in_k_steps(s_zero, c1, max_k=1)
    # From 1 term, identify into itself is not allowed or leaves 0 terms?
    # Identifying requires 2 terms. So 1 term cannot identify to 0 terms.
    assert not res_k1.restored


def test_addition_leaves_nothing() -> None:
    """Additions of terms or assertions leave nothing under 1-step and 2-step."""
    s = DState(2, (0, 0, 0, 0), (0, 0, 0, 0), names=None)
    c_term = Change(Kind.ADD_TERM, "", 2, 0)
    c_assn = Change(Kind.ADD_ASSERTION, "r", 0, 1)


    assert leftover_of_one_step(s, c_term) is LeftOver.NOTHING_LEFT
    assert leftover_of_two_step(s, c_term) is LeftOver.NOTHING_LEFT

    assert leftover_of_one_step(s, c_assn) is LeftOver.NOTHING_LEFT
    assert leftover_of_two_step(s, c_assn) is LeftOver.NOTHING_LEFT


def test_removal_always_clearable() -> None:
    """Removal of an assertion is always clearable in 1 step, hence in <= 2 steps."""
    s = DState(2, (0, 1, 0, 0), (0, 0, 0, 0), names=None)
    c_rem = Change(Kind.REMOVE, "r", 0, 1)

    assert leftover_of_one_step(s, c_rem) is LeftOver.CLEARABLE
    assert leftover_of_two_step(s, c_rem) is LeftOver.CLEARABLE

    seq1 = clearing_sequence_one(s, c_rem)
    assert seq1 is not None
    assert len(seq1) == 1
    assert seq1[0].kind is Kind.ADD_ASSERTION
    assert seq1[0].rel == "r"
    assert seq1[0].x == 0 and seq1[0].y == 1

    seq2 = clearing_sequence_two(s, c_rem)
    assert seq2 is not None
    assert len(seq2) == 1


def test_identification_bare_term() -> None:
    """Identifying a bare term into another term is clearable in 1 step and 2 steps."""
    # Term 0 has loop (0, 0), term 1 is bare
    s = DState(2, (1, 0, 0, 0), (0, 0, 0, 0), names=None)
    assert not bare(s, 0)
    assert bare(s, 1)

    c_id = Change(Kind.IDENTIFY, "", 0, 1)
    assert leftover_of_one_step(s, c_id) is LeftOver.CLEARABLE
    assert leftover_of_two_step(s, c_id) is LeftOver.CLEARABLE

    seq1 = clearing_sequence_one(s, c_id)
    assert seq1 is not None
    assert len(seq1) == 1
    assert seq1[0].kind is Kind.ADD_TERM

    seq2 = clearing_sequence_two(s, c_id)
    assert seq2 is not None
    assert len(seq2) == 1


def test_identification_non_bare_terms_and_three_step_witness() -> None:
    """Identifying two non-bare terms cannot be cleared in 1 or 2 steps, but can be cleared in 3 steps."""
    # S has 2 terms with assertion 0 -> 1 in r. Neither 0 nor 1 is bare.
    s = DState(2, (0, 1, 0, 0), (0, 0, 0, 0), names=None)
    assert not bare(s, 0)
    assert not bare(s, 1)

    c_id = Change(Kind.IDENTIFY, "", 0, 1)
    assert leftover_of_one_step(s, c_id) is LeftOver.UNCLEARED
    assert leftover_of_two_step(s, c_id) is LeftOver.UNCLEARED

    assert clearing_sequence_one(s, c_id) is None
    assert clearing_sequence_two(s, c_id) is None

    # But 3 steps can clear it!
    seq3 = clearing_sequence_three(s, c_id)
    assert seq3 is not None
    assert len(seq3) == 3

    witness = three_step_restoration_witness()
    assert witness["bare_0"] is False
    assert witness["bare_1"] is False
    assert witness["restores_1"] is False
    assert witness["restores_2"] is False
    assert witness["restores_3"] is True


def test_parity_analysis() -> None:
    """Test Size Parity Invariant on all change kinds."""
    s = DState(2, (0, 1, 0, 0), (0, 0, 0, 0), names=None)

    # Identification
    c_id = Change(Kind.IDENTIFY, "", 0, 1)
    p_id = parity_analysis(s, c_id)
    assert p_id.start_size == 3  # 2 terms + 1 assertion
    assert p_id.outcome_size == 2  # 1 term + 1 loop
    assert p_id.size_delta == -1
    assert p_id.restoration_requires_delta == 1
    assert p_id.exact_two_step_restoration_possible is False

    # Removal
    c_rem = Change(Kind.REMOVE, "r", 0, 1)
    p_rem = parity_analysis(s, c_rem)
    assert p_rem.start_size == 3
    assert p_rem.outcome_size == 2  # 2 terms + 0 assertions
    assert p_rem.size_delta == -1
    assert p_rem.restoration_requires_delta == 1
    assert p_rem.exact_two_step_restoration_possible is False

    # Addition
    c_add = Change(Kind.ADD_TERM, "", 2, 0)

    p_add = parity_analysis(s, c_add)
    assert p_add.start_size == 3
    assert p_add.outcome_size == 4
    assert p_add.size_delta == 1
    assert p_add.restoration_requires_delta == -1
    assert p_add.exact_two_step_restoration_possible is False


def test_compare_all_leftovers_on_edge_cases() -> None:
    """Verify zero discrepancies across handcrafted edge cases."""
    edge_states = generate_edge_case_states()
    comp = compare_all_leftovers(edge_states)
    assert comp["coincides"] is True
    assert comp["discrepancies"] == []
    assert comp["length_two_restorations"] == 0
    assert comp["total_checked"] > 0


def test_independent_classification_census() -> None:
    """Verify independent census runs with zero discrepancies."""
    census = independent_classification_census(runs=((2, 4),))
    for key, data in census.items():
        comp = data["comparison"]
        assert comp["coincides"] is True
        assert comp["discrepancies"] == []
        assert comp["length_two_restorations"] == 0


def test_verify_falsifier() -> None:
    """Verify the top-level falsifier confirmation."""
    res = verify_falsifier(runs=((2, 4),))
    assert res["hypothesis_status"] == "REFUTED"
    assert res["falsifier_status"] == "CONFIRMED"
    assert res["all_runs_coincide"] is True
    assert res["size_parity_invariant_holds"] is True
    assert res["three_step_witness"]["restores_3"] is True


def test_step3_failure_unrestorable() -> None:
    """Test restores_in_k_steps with max_k=3 on a state where 3 steps cannot restore it."""
    # S has 3 terms in a directed 3-cycle: 0->1, 1->2, 2->0 in r
    r_cycle = [0] * 9
    r_cycle[0 * 3 + 1] = 1
    r_cycle[1 * 3 + 2] = 1
    r_cycle[2 * 3 + 0] = 1
    s = DState(3, tuple(r_cycle), (0,) * 9, names=None)
    # Identifying 0 and 1 creates two loops and an edge. In 3 steps, it cannot restore S.
    c = Change(Kind.IDENTIFY, "", 0, 1)
    res = restores_in_k_steps(s, c, max_k=3)
    assert not res.restored
    assert res.length == 0
    assert res.sequence == ()
    assert clearing_sequence_three(s, c) is None


def test_differential_injections(monkeypatch: object) -> None:
    """Injection test for compare_all_leftovers recording discrepancies and 2-step restorations."""
    import pytest
    mp = pytest.MonkeyPatch()
    s = DState(2, (0, 0, 0, 0), (0, 0, 0, 0), names=None)

    # Force a discrepancy
    import model
    mp.setattr(model, "leftover_of_one_step", lambda st, ch: LeftOver.UNCLEARED)
    comp = compare_all_leftovers([s])
    assert len(comp["discrepancies"]) > 0
    assert comp["coincides"] is False

    # Force a length-2 restoration record
    from model import RestorationResult
    mp.setattr(
        model,
        "restores_in_k_steps",
        lambda st, ch, max_k: RestorationResult(
            restored=True,
            length=2,
            sequence=(Change(Kind.ADD_TERM, "", 2, 0), Change(Kind.ADD_TERM, "", 3, 0)),
        ),
    )
    comp2 = compare_all_leftovers([s])
    assert comp2["length_two_restorations"] > 0
    assert comp2["coincides"] is False
    mp.undo()


# --- Evidence Generation and Verification Tests ---


def test_evidence_build_structure() -> None:
    """Verify build_evidence produces canonical schema with valid receipts."""
    ev_custom = build_evidence(runs=((2, 2),))
    assert ev_custom["problem"] == "meta/next_ten/09-two-step-leftover"
    assert ev_custom["parent_derivation"] == "tenth"
    assert "seed_change" in ev_custom
    assert ev_custom["formal_claim"]["hypothesis_status"] == "REFUTED"
    assert ev_custom["formal_claim"]["falsifier_status"] == "CONFIRMED"
    assert ev_custom["size_parity_invariant"]["holds"] is True
    assert (
        ev_custom["size_parity_invariant"]["two_step_restoration_algebraically_possible"]
        is False
    )
    assert ev_custom["what_does_not_follow"]["refuted_by_witness"] is True
    assert "witness" in ev_custom["what_does_not_follow"]
    assert "falsification_results" in ev_custom
    assert "census" in ev_custom


def test_evidence_compare_files(tmp_path: Path) -> None:
    """Verify compare_files under missing, matching, and mismatched files."""
    f1 = tmp_path / "f1.txt"
    f2 = tmp_path / "f2.txt"

    # Both missing
    assert not compare_files(f1, f2)

    # One missing
    f1.write_text("hello", encoding="utf-8")
    assert not compare_files(f1, f2)
    assert not compare_files(f2, f1)

    # Both exist, mismatched
    f2.write_text("world", encoding="utf-8")
    assert not compare_files(f1, f2)

    # Both exist, identical
    f2.write_text("hello", encoding="utf-8")
    assert compare_files(f1, f2)


def test_evidence_write_and_cli_out(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Verify write_evidence and CLI --out generation."""
    data = {"sample": "data", "num": 42}
    out_target = write_evidence(tmp_path, data)
    assert out_target.exists()
    loaded = json.loads(out_target.read_text(encoding="utf-8"))
    assert loaded == data

    # Use fast build for CLI test
    monkeypatch.setattr(evidence, "build_evidence", lambda: data)
    cli_out_dir = tmp_path / "cli_out"
    ret = evidence.main(["--out", str(cli_out_dir)])
    assert ret == 0
    assert (cli_out_dir / "evidence.json").exists()
    assert (
        json.loads((cli_out_dir / "evidence.json").read_text(encoding="utf-8")) == data
    )


def test_evidence_cli_check_success_and_failures(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Verify CLI --check passes against fresh directory and catches missing/tampered files."""
    data = {"mock": "evidence_receipt"}
    monkeypatch.setattr(evidence, "build_evidence", lambda: data)

    gen_dir = tmp_path / "valid_ev"
    ret_gen = evidence.main(["--out", str(gen_dir)])
    assert ret_gen == 0

    # Check against valid directory
    ret_check = evidence.main(["--check", "--out", str(gen_dir)])
    assert ret_check == 0

    # Check against directory with missing evidence.json
    empty_dir = tmp_path / "empty_dir"
    empty_dir.mkdir()
    ret_missing = evidence.main(["--check", "--out", str(empty_dir)])
    assert ret_missing == 1

    # Check against directory with tampered evidence.json
    tampered_dir = tmp_path / "tampered_dir"
    ret_tamper_gen = evidence.main(["--out", str(tampered_dir)])
    assert ret_tamper_gen == 0
    (tampered_dir / "evidence.json").write_text("corrupted content", encoding="utf-8")
    ret_tampered = evidence.main(["--check", "--out", str(tampered_dir)])
    assert ret_tampered == 1


def test_evidence_main_dunder(monkeypatch: pytest.MonkeyPatch) -> None:
    """Exercise __main__ execution block and check against canonical evidence.json."""
    monkeypatch.setattr(sys, "argv", [str(_HERE / "evidence.py"), "--check"])
    with pytest.raises(SystemExit) as exc_info:
        runpy.run_path(str(_HERE / "evidence.py"), run_name="__main__")
    assert exc_info.value.code == 0




