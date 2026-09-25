"""Deterministic evidence generator for Problem 03: given first change adding a term.

Generates evidence artifacts into an `evidence/` subdirectory:
1. `exploration_summary.json`: BFS exploration totals and independent orbit census verification.
2. `comparison_with_ninth.json`: Comparison with Ninth parent derivation.
3. `census_counts.csv`: Independent orbit counts by terms and assertions within bound.
4. `reachable_states_sample.csv`: Catalog of explored states showing cost shift of -1.
5. `MANIFEST.sha256`: Cryptographic checksums of generated evidence files.

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

# Ensure derivation directory is on sys.path
HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(HERE))

from model import (  # noqa: E402
    GIVEN_ASSERTIONS,
    GIVEN_SIZE,
    GIVEN_TERMS,
    compare_with_ninth,
    cost,
    cost_ninth,
    cost_shift,
    counts_within,
    explore,
    order,
    verify_exploration_completeness,
)

EVIDENCE_FILES = (
    "exploration_summary.json",
    "comparison_with_ninth.json",
    "census_counts.csv",
    "reachable_states_sample.csv",
)


def compute_sha256(path: Path) -> str:
    """Compute hex SHA-256 digest of a file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_evidence(out_dir: Path) -> list[Path]:
    """Generate all evidence files into out_dir and return their paths."""
    out_dir.mkdir(parents=True, exist_ok=True)
    bound = 3
    rounds = 4

    expl = explore(bound=bound, rounds=rounds, keep_log=True)
    completeness = verify_exploration_completeness(expl)
    comp = compare_with_ninth(bound=bound, rounds=rounds)
    expected_census = counts_within(bound=bound, rounds=rounds)

    written: list[Path] = []

    # 1. exploration_summary.json
    summary_data = {
        "given_terms": GIVEN_TERMS,
        "given_assertions": GIVEN_ASSERTIONS,
        "given_size": GIVEN_SIZE,
        "bound_terms": bound,
        "rounds": rounds,
        "total_results_explored": len(expl.depth),
        "total_results_expected": completeness["total_expected"],
        "census_complete": completeness["complete"],
        "empty_explored": completeness["empty_explored"],
        "new_per_round": expl.new_per_round,
        "attempts_per_round": expl.attempts_per_round,
        "xrx_per_round": expl.xrx_per_round,
        "xsx_per_round": expl.xsx_per_round,
        "frontier_exits_count": len(expl.frontier),
        "disagreements": completeness["disagreements"],
    }
    p_summary = out_dir / "exploration_summary.json"
    p_summary.write_text(json.dumps(summary_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_summary)

    # 2. comparison_with_ninth.json
    comp_data = {
        "root_03_n": comp.root_03.n,
        "root_03_m": comp.root_03.m,
        "root_ninth_n": comp.root_ninth.n,
        "root_ninth_m": comp.root_ninth.m,
        "empty_reachable_in_03": comp.empty_reachable_in_03,
        "empty_reachable_in_ninth": comp.empty_reachable_in_ninth,
        "round_03_of_one_term": comp.round_03_of_one_term,
        "round_ninth_of_one_term": comp.round_ninth_of_one_term,
        "round_03_new_per_round": comp.round_03_new_per_round,
        "round_ninth_new_per_round": comp.round_ninth_new_per_round,
        "cost_shifts": comp.cost_shifts,
        "falsifier_holds": comp.falsifier_holds,
        "hypothesis_supported": comp.hypothesis_supported,
    }
    p_comp = out_dir / "comparison_with_ninth.json"
    p_comp.write_text(json.dumps(comp_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_comp)

    # 3. census_counts.csv
    p_census = out_dir / "census_counts.csv"
    with open(p_census, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow(["terms", "assertions", "expected_orbit_count"])
        for k in sorted(expected_census.keys(), key=lambda x: tuple(map(int, x.split("/")))):
            n_str, t_str = k.split("/")
            writer.writerow([int(n_str), int(t_str), expected_census[k]])
    written.append(p_census)

    # 4. reachable_states_sample.csv
    p_sample = out_dir / "reachable_states_sample.csv"
    with open(p_sample, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow([
            "index",
            "round_03",
            "terms",
            "r_mults",
            "s_mults",
            "size",
            "cost_03",
            "cost_ninth",
            "cost_shift",
            "r_tuple",
            "s_tuple",
        ])
        for idx, s in enumerate(sorted(expl.depth.keys(), key=order)[:50]):
            r_sum = sum(s.r)
            s_sum = sum(s.s)
            writer.writerow([
                idx,
                expl.depth[s],
                s.n,
                r_sum,
                s_sum,
                s.size,
                cost(s),
                cost_ninth(s),
                cost_shift(s),
                " ".join(map(str, s.r)),
                " ".join(map(str, s.s)),
            ])
    written.append(p_sample)

    # 5. MANIFEST.sha256
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
