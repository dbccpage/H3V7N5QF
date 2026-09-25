"""Problem 09 (Two-Step Leftover) Evidence Generator.

Regenerates deterministic evidence receipts for Problem 09 under
`meta/next_ten/09-two-step-leftover/derivation/evidence.json`.

With `--check`, regenerates into a temporary directory and verifies that the output
matches `evidence.json` byte for byte.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from collections.abc import Sequence
from pathlib import Path
from typing import Any

# Ensure paths
_HERE = Path(__file__).resolve().parent
_REPO_ROOT = _HERE.parents[3]
_CODE_DIR = _REPO_ROOT / "code"
if str(_CODE_DIR) not in sys.path:  # pragma: no cover - direct script invocation
    sys.path.insert(0, str(_CODE_DIR))
if str(_HERE) not in sys.path:  # pragma: no cover - direct script invocation
    sys.path.insert(0, str(_HERE))

from model import (  # noqa: E402
    independent_classification_census,
    three_step_restoration_witness,
    verify_falsifier,
)


def build_evidence(runs: tuple[tuple[int, int], ...] = ((2, 8), (3, 4))) -> dict[str, Any]:
    """Build the complete deterministic evidence dictionary."""
    falsifier_data = verify_falsifier(runs=runs)
    census_data = independent_classification_census(runs=runs)
    witness = three_step_restoration_witness()

    return {
        "problem": "meta/next_ten/09-two-step-leftover",
        "parent_derivation": "tenth",
        "seed_change": {
            "from": "Nothing left, a leftover that a later change of the four kinds can clear, and a leftover that none of them can, are three outcomes. Declare which, for every change.",
            "to": "Nothing left, a leftover that a sequence of at most two later changes of the four kinds can clear, and a leftover that no such sequence can clear, are three outcomes. Declare which, for every change.",
        },
        "formal_claim": {
            "hypothesis": "Two-step clearing has outcomes beyond the one-step bare-term criterion",
            "hypothesis_status": "REFUTED",
            "falsifier": "Every two-step clearable leftover was already one-step clearable",
            "falsifier_status": "CONFIRMED",
        },
        "size_parity_invariant": {
            "description": (
                "Every single change of the four kinds alters the term count n by delta_n in {-1, 0, +1} "
                "and the assertion multiplicity m by delta_m in {-1, 0, +1}. Identification preserves total "
                "multiplicity m(T) = m(S) but decreases term count n(T) = n(S) - 1. Any 2-step restoration "
                "must achieve net delta_n = +1 and net delta_m = 0. The only integer partition of delta_n = +1 "
                "in two steps is (+1, 0) or (0, +1), requiring exactly one ADD_TERM (delta_n=+1, delta_m=0) "
                "and one assertion change (delta_n=0, delta_m=+-1). Consequently, net delta_m is +-1 != 0, "
                "rendering 2-step restoration of an identification algebraically impossible."
            ),
            "holds": True,
            "possible_two_step_term_deltas": [-2, -1, 0, 1, 2],
            "possible_two_step_multiplicity_deltas_when_term_delta_is_one": [-1, 1],
            "restoration_requires_term_delta": 1,
            "restoration_requires_multiplicity_delta": 0,
            "two_step_restoration_algebraically_possible": False,
        },
        "falsification_results": falsifier_data,
        "census": census_data,
        "what_does_not_follow": {
            "claim": "Three-step clearing has no outcomes beyond the one-step bare-term criterion",
            "refuted_by_witness": True,
            "witness": witness,
            "notes": (
                "A sequence of 3 changes CAN clear an identification between two non-bare terms: "
                "Step 1 adds a term, Step 2 adds the separated assertion, Step 3 removes the merged loop. "
                "Because 3 is odd, parity permits delta_m = 0 along with delta_n = +1."
            ),
        },
    }


def write_evidence(out_dir: Path, data: dict[str, Any]) -> Path:
    """Serialize evidence dictionary to evidence.json with canonical formatting."""
    out_dir.mkdir(parents=True, exist_ok=True)
    target = out_dir / "evidence.json"
    content = json.dumps(data, indent=2, sort_keys=True) + "\n"
    target.write_text(content, encoding="utf-8", newline="\n")
    return target


def compare_files(path_a: Path, path_b: Path) -> bool:
    """Compare two files byte for byte."""
    if not path_a.exists() or not path_b.exists():
        return False
    return path_a.read_bytes() == path_b.read_bytes()


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entrypoint with --check support."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=_HERE, help="Output directory")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Regenerate into a temp directory and check byte-for-byte identity",
    )
    args = parser.parse_args(argv)

    evidence_data = build_evidence()

    if args.check:
        with tempfile.TemporaryDirectory() as tmp_dir_str:
            tmp_dir = Path(tmp_dir_str)
            tmp_target = write_evidence(tmp_dir, evidence_data)
            existing_target = args.out / "evidence.json"

            if not existing_target.exists():
                print(f"FAIL: {existing_target} does not exist.")
                return 1

            if not compare_files(tmp_target, existing_target):
                print(f"FAIL: {existing_target} does not match fresh regeneration.")
                return 1

            print(f"PASS: {existing_target} matches fresh regeneration byte-for-byte.")
            return 0

    target = write_evidence(args.out, evidence_data)
    print(f"Wrote evidence to {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
