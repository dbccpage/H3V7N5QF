"""Unit tests for Problem 07 (Two-Term Readings) Derivation.

Covers:
- Extraction of 0-, 1-, and 2-term sub-readings.
- Equivalence relation properties: reflexivity, symmetry, transitivity.
- Collapsing of distinct written states (e.g. arb and bra at n=2).
- Collapsing of non-isomorphic states (e.g. 2 edges vs 4 edges at n=3).
- Partition hierarchy at bound 3: Written (69) > FREE canonical (20) > Multiset (14) > Set (8).
- Hypothesis resolution: Local reading equivalence strictly differs from both written equality
  and FREE rewriting.
- Falsifier refutation: The partition does NOT agree with either parent equivalence.
- Step congruence failure: Demonstration that the step transition relation does not descend
  to the quotient.
- Exploration under quotient.
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
if str(ROOT / "code") not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(ROOT / "code"))

from model import (  # noqa: E402
    check_step_congruence,
    explore_quotient,
    extract_records,
    find_smallest_free_collision,
    find_smallest_written_collision,
    record_multiset,
    record_set,
    same_local,
    same_local_multiset,
)
import evidence  # noqa: E402
from xry.state import Sameness, State, canonical, given  # noqa: E402
from eighteenth.explore import explore_written  # noqa: E402
from eighteenth.writing import same_written  # noqa: E402


def test_extract_records_basic() -> None:
    """Test record extraction on elementary states."""
    # 0 terms
    s0 = State(0, 0)
    recs0 = extract_records(s0)
    assert recs0 == [(0, ())]
    assert record_set(s0) == frozenset({(0, ())})

    # 1 term, no loops
    s1 = State(1, 0)
    recs1 = extract_records(s1)
    assert recs1 == [(0, ()), (1, ())]
    assert record_set(s1) == frozenset({(0, ()), (1, ())})

    # 1 term with self-loop (illegal state)
    s1_loop = State.of(1, [(0, 0)])
    recs1_loop = extract_records(s1_loop)
    assert recs1_loop == [(0, ()), (1, ((0, 0),))]
    assert (1, ((0, 0),)) in record_set(s1_loop)

    # 2 terms, 1 edge (arb)
    s2 = State.of(2, [(0, 1)])
    recs2 = extract_records(s2)
    # Total count: 1 (0-term) + 2 (1-term) + 2 (2-term) = 5
    assert len(recs2) == 5
    assert (0, ()) in recs2
    assert (1, ()) in recs2
    assert (2, ((0, 1),)) in recs2
    assert (2, ((1, 0),)) in recs2


def test_extract_records_count_formula() -> None:
    """Every state of n terms generates exactly 1 + n + n*(n-1) = 1 + n^2 records."""
    for n in range(4):
        s = State(n, 0)
        recs = extract_records(s)
        assert len(recs) == 1 + n * n


def test_equivalence_relation_properties() -> None:
    """Local reading equality is an equivalence relation (reflexive, symmetric, transitive)."""
    start = given(False, Sameness.FREE)
    expl = explore_written(start, bound=3, rounds=8)
    sample_states = list(expl.depth.keys())[:15]

    # Reflexivity: s ~ s
    for s in sample_states:
        assert same_local(s, s)
        assert same_local_multiset(s, s)

    # Symmetry: s1 ~ s2 <=> s2 ~ s1
    for s1 in sample_states:
        for s2 in sample_states:
            assert same_local(s1, s2) == same_local(s2, s1)
            assert same_local_multiset(s1, s2) == same_local_multiset(s2, s1)

    # Transitivity: s1 ~ s2 and s2 ~ s3 => s1 ~ s3
    for s1 in sample_states:
        for s2 in sample_states:
            for s3 in sample_states:
                if same_local(s1, s2) and same_local(s2, s3):
                    assert same_local(s1, s3)
                if same_local_multiset(s1, s2) and same_local_multiset(s2, s3):
                    assert same_local_multiset(s1, s3)


def test_smallest_written_collision() -> None:
    """At n=2, arb and bra have identical local records but are distinct written states."""
    s_arb = State.of(2, [(0, 1)])
    s_bra = State.of(2, [(1, 0)])

    assert not same_written(s_arb, s_bra)
    assert same_local(s_arb, s_bra)
    assert same_local_multiset(s_arb, s_bra)

    # Automated search identifies this pair
    pair = find_smallest_written_collision([s_arb, s_bra])
    assert pair is not None
    assert set(pair) == {s_arb, s_bra}


def test_smallest_free_collision() -> None:
    """At n=3, non-isomorphic states have identical local record sets."""
    # State A: 3 terms, 1 2-cycle and 1 isolated vertex (2 assertions)
    s_a = State.of(3, [(0, 1), (1, 0)])
    # State B: 3 terms, 2 2-cycles (4 assertions)
    s_b = State.of(3, [(0, 1), (1, 0), (0, 2), (2, 0)])

    assert canonical(s_a) != canonical(s_b)
    assert s_a.m != s_b.m
    assert same_local(s_a, s_b)

    # Both record sets contain: 0-term, 1-term, 2-term non-edge, 2-term 2-cycle
    expected_records = frozenset({
        (0, ()),
        (1, ()),
        (2, ()),
        (2, ((0, 1), (1, 0))),
    })
    assert record_set(s_a) == expected_records
    assert record_set(s_b) == expected_records

    # Automated search finds a non-isomorphic colliding pair at n=3
    start = given(False, Sameness.FREE)
    expl = explore_written(start, bound=3, rounds=12)
    pair = find_smallest_free_collision(expl.depth.keys())
    assert pair is not None
    s1, s2 = pair
    assert canonical(s1) != canonical(s2)
    assert same_local(s1, s2)


def test_partition_hierarchy_bound_3() -> None:
    """Verify the strict coarseness hierarchy at bound 3:
    Written (69) > FREE canonical (20) > Multiset local (14) > Set local (8).
    """
    start = given(False, Sameness.FREE)
    expl = explore_written(start, bound=3, rounds=12)
    states = list(expl.depth.keys())
    assert len(states) == 69

    written_classes = len({s for s in states})
    assert written_classes == 69

    canonical_classes = len({canonical(s) for s in states})
    assert canonical_classes == 20

    multiset_classes = len({record_multiset(s) for s in states})
    assert multiset_classes == 14

    set_classes = len({record_set(s) for s in states})
    assert set_classes == 8

    # Strict hierarchy
    assert written_classes > canonical_classes > multiset_classes > set_classes


def test_anchored_partition_bound_3() -> None:
    """On anchored states at bound 3:
    137 written states, 109 canonical classes, 8 local record set classes.
    """
    start = given(False, Sameness.ANCHORED)
    expl = explore_written(start, bound=3, rounds=12)
    states = list(expl.depth.keys())
    assert len(states) == 137

    canonical_classes = len({canonical(s) for s in states})
    assert canonical_classes == 109

    set_classes = len({record_set(s) for s in states})
    assert set_classes == 8


def test_hypothesis_resolution() -> None:
    """Hypothesis 'Sameness by local readings differs from both written equality and
    FREE rewriting' is confirmed; Falsifier 'The bounded partitions agree with one
    of the parent's two equivalences' is refuted.
    """
    start = given(False, Sameness.FREE)
    expl = explore_written(start, bound=3, rounds=12)
    states = list(expl.depth.keys())

    written_count = len(states)
    canonical_count = len({canonical(s) for s in states})
    local_count = len({record_set(s) for s in states})

    # The local readings partition has 8 classes, while written has 69 and canonical has 20
    assert local_count != written_count
    assert local_count != canonical_count
    assert local_count == 8
    assert written_count == 69
    assert canonical_count == 20


def test_step_congruence_fails() -> None:
    """The one-step transition system does NOT descend to equivalence classes."""
    start = given(False, Sameness.FREE)
    expl = explore_written(start, bound=3, rounds=12)

    congruent, failures = check_step_congruence(expl.depth.keys(), max_terms=3)
    assert not congruent
    assert len(failures) > 0

    # Inspect the first failure
    first = failures[0]
    assert same_local(first.state_a, first.state_b)
    assert first.reachable_classes_a != first.reachable_classes_b


def test_explore_quotient() -> None:
    """Quotient exploration tracks round-by-round class discovery."""
    start = given(False, Sameness.FREE)
    q_expl = explore_quotient(start, bound=3, rounds=12)

    assert q_expl.total_written_states == 69
    assert q_expl.distinct_quotient_classes == 8
    # Classes are discovered in early rounds
    assert sum(q_expl.new_classes_per_round) == 8
    assert len(q_expl.class_members) == 8
    assert len(q_expl.canonical_forms_per_class) == 8

    # Some quotient classes contain multiple distinct canonical forms
    collapsing_classes = [
        rec for rec, canons in q_expl.canonical_forms_per_class.items() if len(canons) > 1
    ]
    assert len(collapsing_classes) > 0


def test_edge_cases_and_empty_pool() -> None:
    """Check collision searches on singletons or states with no collisions."""
    # Empty pool
    assert find_smallest_written_collision([]) is None
    assert find_smallest_free_collision([]) is None

    # Singleton pool
    s = State.of(2, [(0, 1)])
    assert find_smallest_written_collision([s]) is None
    assert find_smallest_free_collision([s]) is None

    # Pool with no FREE collisions (e.g. only s_arb and s_bra, which are isomorphic)
    s_arb = State.of(2, [(0, 1)])
    s_bra = State.of(2, [(1, 0)])
    assert find_smallest_free_collision([s_arb, s_bra]) is None


def test_evidence_data_and_cli(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Test evidence generation and CLI verification."""
    data = evidence.generate_evidence_data()
    assert data["problem"] == "07-two-term-readings"
    hyp_res = data["hypothesis_resolution"]
    assert isinstance(hyp_res, dict)
    assert hyp_res["hypothesis_confirmed"] is True

    # Test main() generating file to temporary location
    fake_evidence_file = tmp_path / "evidence.json"
    monkeypatch.setattr(evidence, "EVIDENCE_FILE", fake_evidence_file)

    # First run without --check writes the file
    exit_code = evidence.main([])
    assert exit_code == 0
    assert fake_evidence_file.exists()

    # Second run with --check passes byte-identically
    exit_code_check = evidence.main(["--check"])
    assert exit_code_check == 0

    # Corrupt the file to test check failure
    fake_evidence_file.write_text("{\"corrupted\": true}\n", encoding="utf-8")
    exit_code_fail = evidence.main(["--check"])
    assert exit_code_fail == 1

    # Remove the file to test missing file check failure
    fake_evidence_file.unlink()
    exit_code_missing = evidence.main(["--check"])
    assert exit_code_missing == 1

