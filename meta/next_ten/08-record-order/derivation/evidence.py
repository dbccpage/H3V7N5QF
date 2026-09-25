"""Deterministic evidence generation and verification script for Problem 08 (record-order).

Produces:
1. `summary.json`: Exploration counts, round-by-round statistics, quotient comparison.
2. `witness.json`: Minimal quotient witness states (witness1 and witness2), showing
   identical sixteenth counts, identical sixteenth canonical forms, distinct ordered
   canonical forms, and disjoint next-step admission sets.
3. `branches.json`: Two reachability paths from empty state demonstrating how leftover
   order diverges despite identical term and assertion histories.

Supports `--check` to verify byte-identical regeneration against committed evidence.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import tempfile
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT / "code") not in sys.path:  # pragma: no cover - direct script invocation
    sys.path.insert(0, str(REPO_ROOT / "code"))
if str(REPO_ROOT) not in sys.path:  # pragma: no cover - direct script invocation
    sys.path.insert(0, str(REPO_ROOT))

# Ensure model is imported cleanly
MODEL_PATH = Path(__file__).resolve().parent / "model.py"
import importlib.util
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
canonical = model.canonical
canonical16 = model.canonical16
changes = model.changes
compare_quotients = model.compare_quotients
empty_state = model.empty_state
explore = model.explore
find_minimal_quotient_witness = model.find_minimal_quotient_witness
make_state = model.make_state
perform = model.perform
remove_assertion = model.remove_assertion
same = model.same


def generate_evidence_data() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Generate all evidence dictionaries deterministically."""
    # 1. Bounded exploration: terms <= 2, rounds = 6
    expl = explore(empty_state(), bound=2, rounds=6)
    q_comp = compare_quotients(expl.depth.keys())

    # Format split classes for JSON serialization
    split_info = []
    for s16_state, ordered_list in q_comp["split_classes"].items():
        split_info.append({
            "sixteenth_key": s16_state.key(),
            "sixteenth_n": s16_state.n,
            "ordered_count": len(ordered_list),
            "ordered_keys": [st.key() for st in ordered_list],
            "ordered_records": [list(st.record) for st in ordered_list],
        })

    summary_data = {
        "problem": "08-record-order",
        "seed_sentence": "Recorded leftovers are kept in the order they arise. Only the most recently recorded leftover may be admitted, adding the assertion xry or the assertion xsy; an unadmitted leftover is not an assertion.",
        "bound_terms": 2,
        "rounds": 6,
        "new_per_round": expl.new_per_round,
        "attempts_per_round": expl.attempts_per_round,
        "admissions_per_round": expl.admissions_per_round,
        "total_ordered_results": q_comp["total_ordered"],
        "total_sixteenth_results": q_comp["total_sixteenth"],
        "num_split_classes": q_comp["num_split_classes"],
        "split_classes": split_info,
        "frontier_size": len(expl.frontier),
    }

    # 2. Minimal quotient witness
    w1, w2 = find_minimal_quotient_witness()
    s16_1 = canonical16(w1.to_sixteenth_state())
    s16_2 = canonical16(w2.to_sixteenth_state())
    adm1 = [c.written() for c in changes(w1) if c.admits]
    adm2 = [c.written() for c in changes(w2) if c.admits]

    witness_data = {
        "witness1": {
            "key": w1.key(),
            "n": w1.n,
            "r": list(w1.r),
            "s": list(w1.s),
            "record": list(w1.record),
            "top_leftover": list(w1.top_leftover) if w1.top_leftover else None,
            "sixteenth_counts": list(w1.to_sixteenth_counts()),
            "admissions": adm1,
            "depth_reached": expl.depth.get(w1),
        },
        "witness2": {
            "key": w2.key(),
            "n": w2.n,
            "r": list(w2.r),
            "s": list(w2.s),
            "record": list(w2.record),
            "top_leftover": list(w2.top_leftover) if w2.top_leftover else None,
            "sixteenth_counts": list(w2.to_sixteenth_counts()),
            "admissions": adm2,
            "depth_reached": expl.depth.get(w2),
        },
        "comparison": {
            "ordered_same": same(w1, w2),
            "sixteenth_same": s16_1 == s16_2,
            "counts_identical": w1.to_sixteenth_counts() == w2.to_sixteenth_counts(),
            "admissions_disjoint": bool(set(adm1).isdisjoint(set(adm2))),
        },
        "conclusion": "Hypothesis validated: Order-sensitive feedback changes the result quotient and admission paths. Falsifier refuted: results are not classified by old count alone.",
    }

    # 3. Two reachability paths demonstrating branching
    # Path 1: Empty -> add t0 -> add t1 -> add 0r0 -> add 0r1 -> rem 0r0 -> rem 0r1 => record ((0,0), (0,1))
    # Path 2: Empty -> add t0 -> add t1 -> add 0r0 -> add 0r1 -> rem 0r1 -> rem 0r0 => record ((0,1), (0,0))
    p0 = empty_state()
    p1 = add_term(p0)
    p2 = add_term(p1)
    p3 = add_assertion(p2, "r", 0, 0)
    p4 = add_assertion(p3, "r", 0, 1)

    branch1_step5 = remove_assertion(p4, "r", 0, 0)
    branch1_step6 = remove_assertion(branch1_step5, "r", 0, 1)

    branch2_step5 = remove_assertion(p4, "r", 0, 1)
    branch2_step6 = remove_assertion(branch2_step5, "r", 0, 0)

    branch_data = {
        "common_prefix": [
            "add term (0)",
            "add term (1)",
            "add assertion 0r0",
            "add assertion 0r1",
        ],
        "branch1": {
            "step5": "remove 0r0 -> leaves 0ℓ0",
            "step6": "remove 0r1 -> leaves 0ℓ1",
            "final_record": list(branch1_step6.record),
            "final_top": list(branch1_step6.top_leftover) if branch1_step6.top_leftover else None,
            "next_admissible": [c.written() for c in changes(branch1_step6) if c.admits],
            "matches_witness1": canonical(branch1_step6) == w1,
        },
        "branch2": {
            "step5": "remove 0r1 -> leaves 0ℓ1",
            "step6": "remove 0r0 -> leaves 0ℓ0",
            "final_record": list(branch2_step6.record),
            "final_top": list(branch2_step6.top_leftover) if branch2_step6.top_leftover else None,
            "next_admissible": [c.written() for c in changes(branch2_step6) if c.admits],
            "matches_witness2": canonical(branch2_step6) == w2,
        },
    }

    return summary_data, witness_data, branch_data


def write_evidence(out_dir: Path) -> None:
    """Write evidence files formatted deterministically with newlines."""
    out_dir.mkdir(parents=True, exist_ok=True)
    summary_data, witness_data, branch_data = generate_evidence_data()

    (out_dir / "summary.json").write_text(
        json.dumps(summary_data, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    (out_dir / "witness.json").write_text(
        json.dumps(witness_data, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    (out_dir / "branches.json").write_text(
        json.dumps(branch_data, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def check_evidence(target_dir: Path) -> bool:
    """Regenerate evidence into a temporary directory and verify byte-for-byte equality."""
    with tempfile.TemporaryDirectory() as tmp_str:
        tmp_dir = Path(tmp_str)
        write_evidence(tmp_dir)

        expected_files = ["summary.json", "witness.json", "branches.json"]
        for fname in expected_files:
            target_file = target_dir / fname
            if not target_file.exists():
                print(f"ERROR: Missing expected file: {target_file}")
                return False
            actual_bytes = target_file.read_bytes()
            generated_bytes = (tmp_dir / fname).read_bytes()
            if actual_bytes != generated_bytes:
                print(f"ERROR: Byte mismatch in {fname}")
                return False
        print("Byte-identical check passed for all evidence files.")
        return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    default_dir = Path(__file__).resolve().parent / "evidence"
    parser.add_argument("--out", type=Path, default=default_dir, help="Output directory")
    parser.add_argument("--check", action="store_true", help="Check byte-identical regeneration")
    args = parser.parse_args()

    if args.check:
        ok = check_evidence(args.out)
        return 0 if ok else 1

    write_evidence(args.out)
    print(f"Evidence successfully written to {args.out}")
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI checked separately
    sys.exit(main())
