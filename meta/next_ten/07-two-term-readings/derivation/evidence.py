"""Problem 07 (Two-Term Readings) Evidence Script.

Generates deterministic evidence JSON summarizing the local reading quotient,
comparison against eighteenth (written) and base (FREE canonical) sameness,
smallest colliding pairs, and step congruence failure.

Supports `--check` to verify that evidence regenerates byte-identically.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

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
    find_smallest_free_collision,
    find_smallest_written_collision,
    record_multiset,
    record_set,
    same_local,
)
from eighteenth.explore import explore_written  # noqa: E402
from eighteenth.writing import same_written  # noqa: E402
from xry.state import Sameness, canonical, given  # noqa: E402

EVIDENCE_FILE = HERE / "evidence.json"


def generate_evidence_data() -> dict[str, object]:
    """Compute the deterministic evidence data dictionary."""
    start_free = given(False, Sameness.FREE)
    start_anchored = given(False, Sameness.ANCHORED)

    expl_free = explore_written(start_free, bound=3, rounds=12)
    expl_anchored = explore_written(start_anchored, bound=3, rounds=12)

    free_states = list(expl_free.depth.keys())
    anchored_states = list(expl_anchored.depth.keys())

    written_count_free = len(free_states)
    canonical_count_free = len({canonical(s) for s in free_states})
    multiset_count_free = len({record_multiset(s) for s in free_states})
    set_count_free = len({record_set(s) for s in free_states})

    written_count_anchored = len(anchored_states)
    canonical_count_anchored = len({canonical(s) for s in anchored_states})
    set_count_anchored = len({record_set(s) for s in anchored_states})

    # Smallest colliding written pair
    written_pair = find_smallest_written_collision(free_states)
    assert written_pair is not None
    s_w1, s_w2 = written_pair

    # Smallest colliding non-isomorphic pair
    free_pair = find_smallest_free_collision(free_states)
    assert free_pair is not None
    s_f1, s_f2 = free_pair

    # Step congruence test
    congruent, failures = check_step_congruence(free_states, max_terms=3)

    # Quotient exploration
    q_expl = explore_quotient(start_free, bound=3, rounds=12)

    return {
        "problem": "07-two-term-readings",
        "parent_derivation": "eighteenth",
        "seed_edit": (
            "A reading names at most two terms and records the assertions between them. "
            "Two results are the same if every such reading gives the same record."
        ),
        "parameters": {
            "bound_terms": 3,
            "max_rounds": 12,
        },
        "partitions_free": {
            "written_classes": written_count_free,
            "free_canonical_classes": canonical_count_free,
            "multiset_local_classes": multiset_count_free,
            "set_local_classes": set_count_free,
            "hierarchy_holds": (
                written_count_free > canonical_count_free > multiset_count_free > set_count_free
            ),
        },
        "partitions_anchored": {
            "written_classes": written_count_anchored,
            "anchored_canonical_classes": canonical_count_anchored,
            "set_local_classes": set_count_anchored,
        },
        "hypothesis_resolution": {
            "hypothesis": "Sameness by local readings differs from both written equality and FREE rewriting.",
            "hypothesis_confirmed": (
                set_count_free != written_count_free and set_count_free != canonical_count_free
            ),
            "falsifier": "The bounded partitions agree with one of the parent's two equivalences.",
            "falsifier_refuted": (
                set_count_free != written_count_free and set_count_free != canonical_count_free
            ),
        },
        "smallest_written_collision": {
            "state_a_key": s_w1.key(),
            "state_a_written": s_w1.written(),
            "state_b_key": s_w2.key(),
            "state_b_written": s_w2.written(),
            "same_local": same_local(s_w1, s_w2),
            "same_written": same_written(s_w1, s_w2),
        },
        "smallest_free_collision": {
            "state_a_key": s_f1.key(),
            "state_a_canonical": canonical(s_f1).key(),
            "state_a_written": s_f1.written(),
            "state_b_key": s_f2.key(),
            "state_b_canonical": canonical(s_f2).key(),
            "state_b_written": s_f2.written(),
            "same_local": same_local(s_f1, s_f2),
            "canonical_equal": canonical(s_f1) == canonical(s_f2),
        },
        "step_congruence": {
            "descends_to_quotient": congruent,
            "total_failure_witnesses": len(failures),
            "sample_failure": {
                "state_a": failures[0].state_a.key(),
                "state_b": failures[0].state_b.key(),
                "reachable_classes_a_count": len(failures[0].reachable_classes_a),
                "reachable_classes_b_count": len(failures[0].reachable_classes_b),
            }
            if failures
            else None,
        },
        "quotient_exploration": {
            "start_key": start_free.key(),
            "total_written_states": q_expl.total_written_states,
            "distinct_classes": q_expl.distinct_quotient_classes,
            "new_classes_per_round": q_expl.new_classes_per_round,
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    """Generate or check evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify evidence matches committed evidence.json without writing.",
    )
    args = parser.parse_args(argv)

    data = generate_evidence_data()
    serialized = json.dumps(data, indent=2, sort_keys=True) + "\n"

    if args.check:
        if not EVIDENCE_FILE.exists():
            print(f"ERROR: {EVIDENCE_FILE} does not exist for check.", file=sys.stderr)
            return 1
        existing = EVIDENCE_FILE.read_text(encoding="utf-8")
        if existing != serialized:
            print(f"ERROR: {EVIDENCE_FILE} differs from regenerated evidence.", file=sys.stderr)
            return 1
        print("PASS: Evidence verified byte-identically.")
        return 0

    EVIDENCE_FILE.write_text(serialized, encoding="utf-8", newline="\n")
    print(f"Wrote evidence to {EVIDENCE_FILE}")
    print(serialized)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
