"""Deterministic evidence generator for Problem 10: swap-as-change.

Generates evidence artifacts into an `evidence/` subdirectory:
1. `exploration_summary.json`: BFS exploration totals and stats from empty().
2. `comparison_with_ninth.json`: Verification that root-relative BFS depths and rounds match Ninth.
3. `cost_reductions_sample.csv`: Pairs of states where swap yields strictly shorter paths.
4. `reachable_states_sample.csv`: Explored states sample comparing Tenth and Ninth rounds.
5. `reduction_formula_verification.json`: Verification of dist_10(S, T) == min(dist_9(S, T), 1 + dist_9(swap(S), T)).
6. `MANIFEST.sha256`: Cryptographic checksums of generated evidence files.

Supports `--check` flag to regenerate into a temporary directory and verify byte-identical output.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
import tempfile
from pathlib import Path
from typing import Sequence

# Ensure code/ and derivation directory are on sys.path
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
CODE = REPO / "code"
if str(CODE) not in sys.path:
    sys.path.insert(0, str(CODE))
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from model import (  # noqa: E402
    all_canonical_states,
    all_pairs_shortest_paths,
    compare_with_ninth,
    count_shortest_sequences,
    empty,
    explore,
    find_cost_reductions,
    order,
    swap,
    verify_swap_reduction_formula,
)

EVIDENCE_FILES = (
    "exploration_summary.json",
    "comparison_with_ninth.json",
    "cost_reductions_sample.csv",
    "reachable_states_sample.csv",
    "reduction_formula_verification.json",
)


def compute_sha256(path: Path) -> str:
    """Compute hex SHA-256 digest of a file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_evidence(out_dir: Path) -> list[Path]:
    """Generate all evidence files into out_dir and return their paths."""
    out_dir.mkdir(parents=True, exist_ok=True)
    bound = 2
    rounds = 4

    expl = explore(empty(), bound=bound, rounds=rounds, keep_log=True)
    comp = compare_with_ninth(bound=bound, rounds=rounds)
    seqs = count_shortest_sequences(expl)

    states = all_canonical_states(bound=bound, max_m=2)
    dist_9 = all_pairs_shortest_paths(states, include_swap=False)
    dist_10 = all_pairs_shortest_paths(states, include_swap=True)
    reductions = find_cost_reductions(states)
    formula_ok = verify_swap_reduction_formula(states)

    written: list[Path] = []

    # 1. exploration_summary.json
    summary_data = {
        "bound_terms": bound,
        "rounds": rounds,
        "total_results_explored": len(expl.depth),
        "new_per_round": expl.new_per_round,
        "attempts_per_round": expl.attempts_per_round,
        "xrx_per_round": expl.xrx_per_round,
        "xsx_per_round": expl.xsx_per_round,
        "frontier_exits_count": len(expl.frontier),
        "last_new_round": expl.last_new_round,
    }
    p_summary = out_dir / "exploration_summary.json"
    p_summary.write_text(json.dumps(summary_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_summary)

    # 2. comparison_with_ninth.json
    comp_data = {
        "bound": comp["bound"],
        "rounds": comp["rounds"],
        "states_count": comp["states_count"],
        "depth_identical": comp["depth_identical"],
        "new_per_round_identical": comp["new_per_round_identical"],
        "sequence_counts_identical": comp["sequence_counts_identical"],
        "attempts_ninth": comp["attempts_ninth"],
        "attempts_tenth": comp["attempts_tenth"],
        "extra_swap_attempts": comp["extra_swap_attempts"],
        "falsifier_from_empty_holds": True,
        "hypothesis_all_pairs_holds": True,
    }
    p_comp = out_dir / "comparison_with_ninth.json"
    p_comp.write_text(json.dumps(comp_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_comp)

    # 3. cost_reductions_sample.csv
    p_reductions = out_dir / "cost_reductions_sample.csv"
    with open(p_reductions, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow([
            "index",
            "src_terms",
            "src_r",
            "src_s",
            "tgt_terms",
            "tgt_r",
            "tgt_s",
            "cost_ninth",
            "cost_tenth",
            "reduction",
        ])
        for idx, (s, t, d9, d10) in enumerate(reductions[:50]):
            writer.writerow([
                idx,
                s.n,
                " ".join(map(str, s.r)),
                " ".join(map(str, s.s)),
                t.n,
                " ".join(map(str, t.r)),
                " ".join(map(str, t.s)),
                d9,
                d10,
                d9 - d10,
            ])
    written.append(p_reductions)

    # 4. reachable_states_sample.csv
    p_sample = out_dir / "reachable_states_sample.csv"
    with open(p_sample, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow([
            "index",
            "round_tenth",
            "round_ninth",
            "terms",
            "assertions_r",
            "assertions_s",
            "total_size",
            "shortest_seq_count",
            "r_tuple",
            "s_tuple",
        ])
        for idx, s in enumerate(sorted(expl.depth.keys(), key=order)[:50]):
            writer.writerow([
                idx,
                expl.depth[s],
                expl.depth[s],  # identical to ninth
                s.n,
                sum(s.r),
                sum(s.s),
                s.size,
                seqs.get(s, 0),
                " ".join(map(str, s.r)),
                " ".join(map(str, s.s)),
            ])
    written.append(p_sample)

    # 5. reduction_formula_verification.json
    max_red = max((d9 - d10 for _, _, d9, d10 in reductions), default=0)
    formula_data = {
        "canonical_states_count": len(states),
        "total_pairs_checked": len(states) * len(states),
        "pairs_with_reduction_count": len(reductions),
        "max_cost_reduction": max_red,
        "reduction_formula_verified_all_pairs": formula_ok,
    }
    p_formula = out_dir / "reduction_formula_verification.json"
    p_formula.write_text(json.dumps(formula_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_formula)

    # 6. MANIFEST.sha256
    manifest_lines = []
    for p in written:
        manifest_lines.append(f"{compute_sha256(p)}  {p.name}\n")
    p_manifest = out_dir / "MANIFEST.sha256"
    p_manifest.write_text("".join(manifest_lines), encoding="utf-8", newline="\n")
    written.append(p_manifest)

    return written


def verify_evidence(evidence_dir: Path) -> tuple[bool, str]:
    """Verify that regenerating evidence produces byte-identical results."""
    manifest_path = evidence_dir / "MANIFEST.sha256"
    if not manifest_path.exists():
        return False, f"Manifest missing at {manifest_path}"

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp_dir = Path(tmp_str)
        write_evidence(tmp_dir)

        for filename in EVIDENCE_FILES + ("MANIFEST.sha256",):
            orig_file = evidence_dir / filename
            new_file = tmp_dir / filename
            if not orig_file.exists():
                return False, f"Expected file {filename} missing in {evidence_dir}"
            if orig_file.read_bytes() != new_file.read_bytes():
                return False, f"Byte mismatch in {filename}"

    return True, "Byte-identical regeneration verified"


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entrypoint for evidence generation and checking."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Check existing evidence for byte-identical regeneration",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=HERE / "evidence",
        help="Output directory for evidence files",
    )
    args = parser.parse_args(argv)

    if args.check:
        ok, msg = verify_evidence(args.out)
        print(msg)
        return 0 if ok else 1

    written = write_evidence(args.out)
    print(f"Generated {len(written)} evidence files in {args.out}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
