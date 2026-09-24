"""Unit and property tests for Problem 03 derivation.

Testing:
- New root: beginning() has exactly 1 term and 0 assertions.
- Added terms and assertions relative to beginning.
- Attempt counts on beginning and other states.
- Reachability: empty state is unreachable from beginning; states with >= 1 term are reachable.
- Cost shifts: cost_03(s) = size(s) - 1 = cost_ninth(s) - 1 for reachable states; None for empty.
- Exploration completeness against independent orbit counts.
- Comparison with ninth derivation: hypothesis resolution vs falsifier.
"""

from __future__ import annotations

import sys
from pathlib import Path
import pytest

# Ensure derivation package and repo code are accessible
_DERIV_DIR = Path(__file__).resolve().parent
_REPO_ROOT = Path(__file__).resolve().parents[4]
_CODE_DIR = _REPO_ROOT / "code"

for d in (str(_DERIV_DIR), str(_CODE_DIR)):
    if d not in sys.path:
        sys.path.insert(0, d)

from eighth.changes import Change, Kind
from ninth.state import DState, canonical, empty
import model


def test_beginning_properties() -> None:
    """The given beginning has exactly 1 term and 0 assertions."""
    b = model.beginning()
    assert b.n == 1
    assert b.m == 0
    assert b.r == (0,)
    assert b.s == (0,)
    assert b.names is None
    assert model.is_beginning(b)

    # Empty state is not beginning
    assert not model.is_beginning(empty())

    # State with assertions is not beginning
    with_assert = DState(1, (1,), (0,), None)
    assert not model.is_beginning(with_assert)


def test_added_metrics() -> None:
    """A result records how many terms and assertions it adds to what is given."""
    b = model.beginning()
    assert model.added(b) == (0, 0)

    # 2 terms, 1 assertion in r, 2 assertions in s
    s2 = DState(2, (1, 0, 0, 0), (0, 1, 1, 0), None)
    assert model.added(s2) == (1, 3)

    # Error conditions
    named = DState(1, (0,), (0,), (0, 0))
    with pytest.raises(ValueError, match="a state carries no names"):
        model.added(named)

    empty_st = empty()
    with pytest.raises(ValueError, match="state has fewer terms than given beginning"):
        model.added(empty_st)


def test_attempt_counts() -> None:
    """Attempt counts match eighth/ninth rules."""
    b = model.beginning()
    total, additions, xrx, xsx = model.attempt_counts(b)
    # n=1, m=0: C(1,2)=0 identifications, 0 removals, 1 + 2(1)^2 = 3 additions
    assert total == 3
    assert additions == 3
    assert xrx == 1  # adding ara makes xrx loop
    assert xsx == 1  # adding asa makes xsx loop


def test_reachability() -> None:
    """Reachability is governed by having a term."""
    b = model.beginning()
    emp = empty()
    s2 = DState(2, (0, 0, 0, 0), (0, 0, 0, 0), None)

    # From beginning, empty is not reachable
    assert not model.reachable(b, emp)
    assert not model.reachable_from_beginning(emp)

    # From beginning, states with terms are reachable
    assert model.reachable(b, b)
    assert model.reachable_from_beginning(b)
    assert model.reachable(b, s2)
    assert model.reachable_from_beginning(s2)

    # Mutual reachability among states with terms
    assert model.mutual(b, s2)
    assert model.mutual(s2, b)

    # From empty state, everything is reachable
    assert model.reachable(emp, emp)
    assert model.reachable(emp, b)
    assert not model.mutual(emp, b)

    # Names error
    named = DState(1, (0,), (0,), (0, 0))
    with pytest.raises(ValueError, match="a state carries no names"):
        model.reachable(named, b)
    with pytest.raises(ValueError, match="a state carries no names"):
        model.reachable(b, named)


def test_cost_and_cost_shift() -> None:
    """Cost is size - 1 for states with terms, None for empty."""
    b = model.beginning()
    emp = empty()
    assert model.cost(b) == 0
    assert model.cost_ninth(b) == 1
    assert model.cost_shift(b) == -1

    assert model.cost(emp) is None
    assert model.cost_ninth(emp) == 0
    assert model.cost_shift(emp) is None

    # State with 2 terms, 3 assertions: size = 5
    s2 = DState(2, (1, 0, 0, 0), (0, 1, 1, 0), None)
    assert model.cost(s2) == 4
    assert model.cost_ninth(s2) == 5
    assert model.cost_shift(s2) == -1

    # Error handling for names
    named = DState(1, (0,), (0,), (0, 0))
    with pytest.raises(ValueError, match="a state carries no names"):
        model.cost(named)
    with pytest.raises(ValueError, match="a state carries no names"):
        model.cost_ninth(named)


def test_explore_validation() -> None:
    """explore validates its arguments correctly."""
    named = DState(1, (0,), (0,), (0, 0))
    with pytest.raises(ValueError, match="a state carries no names"):
        model.explore(start=named)

    b = model.beginning()
    with pytest.raises(ValueError, match="the bound is below the start"):
        model.explore(bound=0, start=b)

    with pytest.raises(ValueError, match="the bound admits at least one term"):
        model.explore(bound=0, start=empty())

    with pytest.raises(ValueError, match="the number of rounds is not negative"):
        model.explore(rounds=-1)


def test_exploration_results_and_completeness() -> None:
    """Exploration from beginning matches orbit census."""
    expl = model.explore(bound=3, rounds=4, keep_log=True)
    assert expl.start == canonical(model.beginning())
    assert expl.new_per_round[0] == 1  # beginning at round 0
    assert expl.new_per_round[1] == 3  # size 2 states: 1 term with 1 r-loop, 1 term with 1 s-loop, 2 terms 0 assert

    # Verify log was populated
    assert len(expl.log) > 0
    # Verify frontier exits were recorded
    assert len(expl.frontier) > 0

    # Completeness verification
    result = model.verify_exploration_completeness(expl)
    assert result["complete"] is True
    assert result["empty_explored"] is False
    assert result["disagreements"] == {}
    assert result["total_explored"] == result["total_expected"]


def test_verify_exploration_completeness_mismatch() -> None:
    """verify_exploration_completeness detects synthetic corruption."""
    expl = model.explore(bound=2, rounds=2)
    # Artificially inject empty state
    expl.depth[empty()] = 99
    res = model.verify_exploration_completeness(expl)
    assert res["complete"] is False
    assert res["empty_explored"] is True
    assert "0/0" in res["disagreements"]


def test_layer_counts() -> None:
    """layer_counts matches shifted ninth layer counts."""
    layers = model.layer_counts(upto=5)
    # Ninth layer counts from k=1 are: 1, 3, 8, 29, 104, 420
    assert layers[0] == 1
    assert layers[1] == 3
    assert layers[2] == 8
    assert layers[3] == 29
    assert layers[4] == 104
    assert layers[5] == 420


def test_counts_within() -> None:
    """counts_within generates expected terms/total keys."""
    cw = model.counts_within(bound=2, rounds=2)
    # Bound 2, rounds 2: sizes up to rounds + 1 = 3
    # n=1: t <= 2 -> 1/0, 1/1, 1/2
    # n=2: t <= 1 -> 2/0, 2/1
    # n=0 should not be present
    assert "0/0" not in cw
    assert "1/0" in cw
    assert "1/1" in cw
    assert "1/2" in cw
    assert "2/0" in cw
    assert "2/1" in cw


def test_compare_with_ninth() -> None:
    """Comparison with ninth derivation confirms hypothesis and falsifies the falsifier."""
    comp = model.compare_with_ninth(bound=3, rounds=4)
    assert comp.empty_reachable_in_03 is False
    assert comp.empty_reachable_in_ninth is True
    assert comp.round_03_of_one_term == 0
    assert comp.round_ninth_of_one_term == 1
    assert comp.falsifier_holds is False
    assert comp.hypothesis_supported is True
    assert comp.cost_shifts["empty"] is None
    assert comp.cost_shifts["one_term"] == -1


def test_evidence_workflow(tmp_path: Path) -> None:
    """Test evidence generation and verification, including fault injection."""
    import evidence

    # Generate evidence
    out_dir = tmp_path / "evidence"
    files = evidence.write_evidence(out_dir)
    assert len(files) == 5
    assert (out_dir / "MANIFEST.sha256").exists()

    # Verify normal pass
    ok, msg = evidence.verify_evidence(out_dir)
    assert ok is True
    assert "Byte-identical" in msg

    # Verify missing manifest
    no_manifest_dir = tmp_path / "empty_dir"
    no_manifest_dir.mkdir()
    ok_no_man, msg_no_man = evidence.verify_evidence(no_manifest_dir)
    assert ok_no_man is False
    assert "Manifest missing" in msg_no_man

    # Verify missing expected file
    (out_dir / "exploration_summary.json").unlink()
    ok_missing, msg_missing = evidence.verify_evidence(out_dir)
    assert ok_missing is False
    assert "missing in" in msg_missing

    # Verify corrupted content
    (out_dir / "exploration_summary.json").write_text("corrupted", encoding="utf-8")
    ok_corrupt, msg_corrupt = evidence.verify_evidence(out_dir)
    assert ok_corrupt is False
    assert "Byte mismatch" in msg_corrupt

    # Test main CLI entrypoints
    cli_out = tmp_path / "cli_evidence"
    res_gen = evidence.main(["--out", str(cli_out)])
    assert res_gen == 0

    res_check = evidence.main(["--out", str(cli_out), "--check"])
    assert res_check == 0
