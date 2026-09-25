"""Deterministic evidence generator for Problem 06 (Written Budget).

Generates evidence artifacts into an `evidence/` subdirectory:
1. `budget_census.json`: independent census vs BFS exploration counts.
2. `parent_comparison.json`: comparison with Ninth parent derivation.
3. `budgeted_states.csv`: catalog of all 46 reachable canonical budgeted states.
4. `summary.json`: exploration and attempt totals.
5. `MANIFEST.sha256`: cryptographic checksums of generated evidence files.

Supports `--check` flag to regenerate into a temporary directory and verify byte-identity.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Sequence

# Ensure derivation directory is on sys.path
HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(HERE))

from model import (  # noqa: E402
    INITIAL_BUDGET,
    MAX_CHANGES,
    compare_with_parent,
    explore,
    independent_census_counts,
)

EVIDENCE_FILES = (
    "budget_census.json",
    "parent_comparison.json",
    "budgeted_states.csv",
    "summary.json",
)


def compute_sha256(path: Path) -> str:
    """Compute hex SHA-256 digest of a file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_evidence(out_dir: Path) -> list[Path]:
    """Generate all evidence files into `out_dir` and return their paths."""
    out_dir.mkdir(parents=True, exist_ok=True)
    expl = explore(term_bound=4, max_rounds=100)
    census = independent_census_counts()
    comp = compare_with_parent(expl)

    written: list[Path] = []

    # 1. budget_census.json
    census_data = {
        "budget_counts": {str(b): len(states) for b, states in expl.by_budget.items()},
        "census_counts": {str(b): count for b, count in census.items()},
        "census_matches": comp["census_matches"],
        "total_budgeted_states": comp["total_budgeted_states"],
    }
    p_census = out_dir / "budget_census.json"
    p_census.write_text(json.dumps(census_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_census)

    raw_parent_bfs = comp["parent_bfs_wave_sizes"]
    assert isinstance(raw_parent_bfs, dict)
    raw_revisited = comp["revisited_lower_sizes"]
    assert isinstance(raw_revisited, dict)
    comp_data = {
        "budget_counts": {str(b): len(states) for b, states in expl.by_budget.items()},
        "parent_bfs_wave_sizes": {str(r): sz for r, sz in raw_parent_bfs.items()},
        "revisited_lower_sizes": {str(b): pairs for b, pairs in raw_revisited.items()},
        "max_steps": comp["max_steps"],
        "frontier_size": comp["frontier_size"],
    }
    p_comp = out_dir / "parent_comparison.json"
    p_comp.write_text(json.dumps(comp_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_comp)

    # 3. budgeted_states.csv
    p_csv = out_dir / "budgeted_states.csv"
    with open(p_csv, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow([
            "index",
            "budget",
            "round",
            "terms",
            "r_mults",
            "s_mults",
            "size",
            "r_tuple",
            "s_tuple",
        ])
        idx = 0
        for b in range(INITIAL_BUDGET, -1, -1):
            states = expl.by_budget[b]
            for s in states:
                r_sum = sum(s.state.r)
                s_sum = sum(s.state.s)
                writer.writerow([
                    idx,
                    s.budget,
                    INITIAL_BUDGET - s.budget,
                    s.n,
                    r_sum,
                    s_sum,
                    s.size,
                    " ".join(map(str, s.state.r)),
                    " ".join(map(str, s.state.s)),
                ])
                idx += 1
    written.append(p_csv)

    # 4. summary.json
    summary_data = {
        "initial_budget": INITIAL_BUDGET,
        "max_changes": MAX_CHANGES,
        "total_states": len(expl.depth),
        "total_waves": len(expl.waves),
        "attempts_count": expl.attempts_count,
        "performed_count": expl.performed_count,
        "attempts_at_budget_zero": expl.attempts_at_budget_zero,
        "frontier_size": len(expl.frontier),
    }
    p_summary = out_dir / "summary.json"
    p_summary.write_text(json.dumps(summary_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_summary)

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
