"""Tests for Problem 08 derivation (record-order).

Verifies:
1. LIFO admission stack order and blocking of earlier leftovers.
2. Reachability branching producing states with identical sixteenth counts but different order.
3. Term identification remapping endpoints across the ordered sequence.
4. Projection to sixteenth's counted record and quotient refinement.
5. Exploration, change enumeration, and gate compliance.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import pytest

# Dynamically load model.py from the current directory
MODEL_PATH = Path(__file__).resolve().parent / "model.py"
spec = importlib.util.spec_from_file_location("model", MODEL_PATH)
assert spec is not None and spec.loader is not None
model = importlib.util.module_from_spec(spec)
sys.modules["model"] = model
spec.loader.exec_module(model)

Change = model.Change
ChangeKind = model.ChangeKind
OrderedState = model.OrderedState
add_assertion = model.add_assertion
add_term = model.add_term
admit_top = model.admit_top
attempt_counts = model.attempt_counts
canonical = model.canonical
canonical16 = model.canonical16
changes = model.changes
clear_canonical_cache = model.clear_canonical_cache
compare_quotients = model.compare_quotients
empty_state = model.empty_state
explore = model.explore
find_minimal_quotient_witness = model.find_minimal_quotient_witness
identify_terms = model.identify_terms
make_state = model.make_state
perform = model.perform
remove_assertion = model.remove_assertion
rewrite = model.rewrite
same = model.same


def test_empty_and_basic_state() -> None:
    st = empty_state()
    assert st.n == 0
    assert st.size == 0
    assert st.record_len == 0
    assert not st.has_leftover
    assert st.top_leftover is None
    assert st.written() == "empty state"
    assert st.to_sixteenth_counts() == ()

    # Validation errors
    with pytest.raises(ValueError, match="term count cannot be negative"):
        OrderedState(-1, (), (), ())
    with pytest.raises(ValueError, match="relation vectors must have length"):
        OrderedState(1, (0,), (0, 0), ())
    with pytest.raises(ValueError, match="multiplicities cannot be negative"):
        OrderedState(1, (-1,), (0,), ())
    with pytest.raises(ValueError, match="multiplicities cannot be negative"):
        OrderedState(1, (0,), (-1,), ())
    with pytest.raises(ValueError, match="out of range"):
        OrderedState(1, (0,), (0,), ((0, 1),))


def test_make_state_and_properties() -> None:
    st = make_state(2, r_pairs=[(0, 1), (0, 1)], s_pairs=[(1, 0)], record=[(0, 0), (1, 1)])
    assert st.n == 2
    assert st.size == 2 + 2 + 1  # 2 terms + 2 in r + 1 in s
    assert st.record_len == 2
    assert st.has_leftover
    assert st.top_leftover == (1, 1)
    assert st.mult_of("r", 0, 1) == 2
    assert st.mult_of("s", 1, 0) == 1
    assert st.mult_of("r", 1, 0) == 0
    assert st.mult_of("r", 9, 9) == 0  # out of bounds returns 0
    with pytest.raises(ValueError, match="invalid relation"):
        st.mult_of("q", 0, 1)
    assert "0r1(2)" in st.written()
    assert "1s0" in st.written()
    assert "0ℓ0 1ℓ1" in st.written()
    assert st.key() == "2#r:0200#s:0010#rec:0-0.1-1"

    # Validation errors in make_state
    with pytest.raises(ValueError, match="out of bounds"):
        make_state(2, r_pairs=[(2, 0)])
    with pytest.raises(ValueError, match="out of bounds"):
        make_state(2, s_pairs=[(0, 2)])
    with pytest.raises(ValueError, match="out of bounds"):
        make_state(2, record=[(0, 2)])


def test_changes_dataclass() -> None:
    c_term = Change(ChangeKind.ADD_TERM)
    assert c_term.additions == (1, 0)
    assert c_term.written() == "add term"

    c_add = Change(ChangeKind.ADD_ASSERTION, "r", 0, 1, False)
    assert c_add.additions == (0, 1)
    assert c_add.written() == "add 0r1"

    c_adm = Change(ChangeKind.ADD_ASSERTION, "s", 0, 1, True)
    assert c_adm.additions == (0, 1)
    assert c_adm.written() == "admit top leftover 0ℓ1 into s"

    c_id = Change(ChangeKind.IDENTIFY, "", 0, 1)
    assert c_id.additions == (0, 0)
    assert c_id.written() == "identify 0 and 1"

    c_rem = Change(ChangeKind.REMOVE, "s", 0, 0)
    assert c_rem.additions == (0, 0)
    assert c_rem.written() == "remove 0s0"

    with pytest.raises(ValueError, match="relation must be 'r' or 's'"):
        Change(ChangeKind.REMOVE, "invalid", 0, 0)
    with pytest.raises(ValueError, match="identifications and term additions name no relation"):
        Change(ChangeKind.ADD_TERM, "r")
    with pytest.raises(ValueError, match="only an assertion addition can be an admission"):
        Change(ChangeKind.REMOVE, "r", 0, 0, admits=True)


def test_transitions_add_remove_admit() -> None:
    s0 = empty_state()
    s1 = add_term(s0)
    assert s1.n == 1
    s2 = add_term(s1)
    assert s2.n == 2

    # Add assertion
    s3 = add_assertion(s2, "r", 0, 1)
    assert s3.mult_of("r", 0, 1) == 1
    s4 = add_assertion(s3, "s", 0, 1)
    assert s4.mult_of("s", 0, 1) == 1

    # Remove assertion
    s5 = remove_assertion(s4, "r", 0, 1)
    assert s5.mult_of("r", 0, 1) == 0
    assert s5.record == ((0, 1),)

    s6 = remove_assertion(s5, "s", 0, 1)
    assert s6.mult_of("s", 0, 1) == 0
    assert s6.record == ((0, 1), (0, 1))

    # Error handling
    with pytest.raises(ValueError, match="out of bounds"):
        add_assertion(s2, "r", 5, 0)
    with pytest.raises(ValueError, match="invalid relation"):
        add_assertion(s2, "x", 0, 0)
    with pytest.raises(ValueError, match="cannot remove non-asserted pair"):
        remove_assertion(s2, "r", 0, 1)
    with pytest.raises(ValueError, match="cannot remove non-asserted pair"):
        remove_assertion(s2, "s", 0, 1)
    with pytest.raises(ValueError, match="out of bounds"):
        remove_assertion(s2, "r", 9, 0)
    with pytest.raises(ValueError, match="invalid relation"):
        remove_assertion(s2, "z", 0, 0)

    # Admit top
    s7 = admit_top(s6, "r")
    assert s7.mult_of("r", 0, 1) == 1
    assert s7.record == ((0, 1),)

    s8 = admit_top(s7, "s")
    assert s8.mult_of("s", 0, 1) == 1
    assert s8.record == ()

    with pytest.raises(ValueError, match="no leftover available to admit"):
        admit_top(s8, "r")
    with pytest.raises(ValueError, match="invalid relation"):
        admit_top(s6, "x")


def test_lifo_admission_blocking() -> None:
    """Verify that earlier recorded leftovers cannot be admitted until later ones are admitted."""
    s = make_state(2)
    s = add_assertion(s, "r", 0, 0)
    s = add_assertion(s, "r", 0, 1)

    # Remove 0r0 first, then 0r1
    s = remove_assertion(s, "r", 0, 0)  # leaves (0, 0)
    s = remove_assertion(s, "r", 0, 1)  # leaves (0, 1)
    assert s.record == ((0, 0), (0, 1))

    # The available admission changes from changes(s)
    ch_list = changes(s)
    admissions = [c for c in ch_list if c.admits]
    assert len(admissions) == 2
    # Both admissions must admit (0, 1), not (0, 0)
    assert all((c.x, c.y) == (0, 1) for c in admissions)

    # Admitting into r pops (0, 1) and enables (0, 0)
    s_next = perform(s, admissions[0])
    assert s_next.record == ((0, 0),)
    next_admissions = [c for c in changes(s_next) if c.admits]
    assert len(next_admissions) == 2
    assert all((c.x, c.y) == (0, 0) for c in next_admissions)


def test_identify_preserves_leftover_order_and_remaps() -> None:
    s = make_state(3, record=[(0, 2), (2, 1), (1, 0)])
    # Identify 1 and 2
    s_id = identify_terms(s, 1, 2)
    assert s_id.n == 2
    # In original: (0, 2), (2, 1), (1, 0)
    # term 2 maps to 1, term 1 stays 1, term 0 stays 0
    # Expected remapped record: ((0, 1), (1, 1), (1, 0))
    assert s_id.record == ((0, 1), (1, 1), (1, 0))

    # Error handling
    with pytest.raises(ValueError, match="invalid identification pair"):
        identify_terms(s, 2, 1)
    with pytest.raises(ValueError, match="invalid identification pair"):
        identify_terms(s, 0, 5)


def test_rewrite_and_canonical() -> None:
    clear_canonical_cache()
    s = make_state(2, r_pairs=[(0, 1)], record=[(1, 0)])
    # Permutation (1, 0) swaps term 0 and term 1
    s_swapped = rewrite(s, (1, 0))
    assert s_swapped.mult_of("r", 1, 0) == 1
    assert s_swapped.record == ((0, 1),)

    assert same(s, s_swapped)
    assert canonical(s) == canonical(s_swapped)

    with pytest.raises(ValueError, match="permutation length must match n"):
        rewrite(s, (0,))


def test_minimal_quotient_witness() -> None:
    """Validate the minimal witness that refutes the falsifier."""
    w1, w2 = find_minimal_quotient_witness()
    assert w1.n == 2 and w2.n == 2
    assert w1.record == ((0, 0), (0, 1))
    assert w2.record == ((0, 1), (0, 0))

    # In the ordered model, they are distinct results
    assert not same(w1, w2)

    # In sixteenth, they project to the same counted state
    assert w1.to_sixteenth_counts() == (1, 1, 0, 0)
    assert w2.to_sixteenth_counts() == (1, 1, 0, 0)
    s16_1 = w1.to_sixteenth_state()
    s16_2 = w2.to_sixteenth_state()
    assert canonical16(s16_1) == canonical16(s16_2)

    # Admissible sets are strictly disjoint
    adm_w1 = {(c.x, c.y) for c in changes(w1) if c.admits}
    adm_w2 = {(c.x, c.y) for c in changes(w2) if c.admits}
    assert adm_w1 == {(0, 1)}
    assert adm_w2 == {(0, 0)}
    assert adm_w1.isdisjoint(adm_w2)


def test_attempt_counts_and_order() -> None:
    s = make_state(2, r_pairs=[(0, 0)], record=[(0, 1)])
    total, direct, adm = attempt_counts(s)
    ch = changes(s)
    assert len(ch) == total
    assert sum(1 for c in ch if c.kind in (ChangeKind.ADD_TERM, ChangeKind.ADD_ASSERTION) and not c.admits) == direct
    assert sum(1 for c in ch if c.admits) == adm == 2

    # Empty state counts
    s_empty = empty_state()
    tot_e, dir_e, adm_e = attempt_counts(s_empty)
    assert tot_e == 1
    assert dir_e == 1
    assert adm_e == 0
    assert len(changes(s_empty)) == 1


def test_exploration_and_quotient_comparison() -> None:
    start = empty_state()
    res = explore(start, bound=2, rounds=6)
    assert len(res.new_per_round) == 7
    assert res.new_per_round[0] == 1  # empty state
    assert res.new_per_round[1] == 1  # 1 term
    assert sum(res.new_per_round) == len(res.depth)
    assert len(res.frontier) > 0  # adding 3rd term leaves bound=2

    # Compare quotients
    comp = compare_quotients(res.depth.keys())
    assert comp["total_ordered"] == len(res.depth)
    assert comp["total_sixteenth"] < comp["total_ordered"]
    assert comp["num_split_classes"] > 0

    # Ensure minimal witness states are present in explored set
    w1, w2 = find_minimal_quotient_witness()
    assert w1 in res.depth
    assert w2 in res.depth
    assert res.depth[w1] == 6
    assert res.depth[w2] == 6


def test_evidence_generation_and_check(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    EVIDENCE_PATH = Path(__file__).resolve().parent / "evidence.py"
    spec_ev = importlib.util.spec_from_file_location("evidence", EVIDENCE_PATH)
    assert spec_ev is not None and spec_ev.loader is not None
    evidence = importlib.util.module_from_spec(spec_ev)
    sys.modules["evidence"] = evidence
    spec_ev.loader.exec_module(evidence)

    # Test generation
    s_data, w_data, b_data = evidence.generate_evidence_data()
    assert s_data["problem"] == "08-record-order"
    assert w_data["comparison"]["counts_identical"]
    assert b_data["branch1"]["matches_witness1"]
    assert b_data["branch2"]["matches_witness2"]

    # Test write_evidence and check_evidence
    evidence.write_evidence(tmp_path)
    assert evidence.check_evidence(tmp_path)

    # Test check failure on missing file
    (tmp_path / "summary.json").unlink()
    assert not evidence.check_evidence(tmp_path)

    # Test check failure on byte mismatch
    evidence.write_evidence(tmp_path)
    (tmp_path / "summary.json").write_bytes(b"corrupted data")
    assert not evidence.check_evidence(tmp_path)

    # Test main CLI
    ev_dir = Path(__file__).resolve().parent / "evidence"
    monkeypatch.setattr(sys, "argv", ["evidence.py", "--check", "--out", str(ev_dir)])
    assert evidence.main() == 0

    monkeypatch.setattr(sys, "argv", ["evidence.py", "--out", str(tmp_path)])
    assert evidence.main() == 0
