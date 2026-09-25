"""Deterministic evidence generator for Problem 05: Refusal Memory.

Parent derivation: seventeenth.

Artifacts generated:
1. `summary.json`: exploration totals, round distributions, loop discovery rounds.
2. `comparison.json`: seventeenth A-replace vs Problem 05 refusal memory vs seventeenth A-perform.
3. `frontier.json`: exact bounded frontier cuts and unexpanded counts.
4. `census.json`: independent census counts.
5. `MANIFEST.sha256`: cryptographic hashes of generated artifacts.

Supports `--check` flag to regenerate into a temporary directory and verify byte-identity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Sequence

HERE = Path(__file__).resolve().parent
ROOT = Path(__file__).resolve().parents[4]
if str(HERE) not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(HERE))
if str(ROOT / "code") not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(ROOT / "code"))

from model import (
    Closure,
    RefusalState,
    closure,
    independent_census,
    loopfree_census,
)
from seventeenth.explore import closure_perform as seventeenth_closure_perform
from seventeenth.explore import closure_unobstructed as seventeenth_closure_replace
from xry.state import Sameness, given

EVIDENCE_FILES = (
    "summary.json",
    "comparison.json",
    "frontier.json",
    "census.json",
)


def compute_sha256(path: Path) -> str:
    """Compute hex SHA-256 digest of a file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generate_all_evidence(out_dir: Path) -> list[Path]:
    """Generate all evidence artifacts into `out_dir`."""
    out_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []

    # 1. Summary of explorations across settings
    summary_data: dict[str, object] = {}
    runs: dict[str, Closure] = {}

    for bra in (False, True):
        for sameness in (Sameness.ANCHORED, Sameness.FREE):
            run_key = f"bra_{bra}_{sameness.value}"
            start = given(bra, sameness)
            # Explore under refusal memory: bound 3, 4 rounds
            cl = closure(start, bound=3, rounds=4, enter_obstructed=False, keep_log=True)
            runs[run_key] = cl

            # Count by round
            by_round: dict[int, int] = {}
            for s, r in cl.depth.items():
                by_round[r] = by_round.get(r, 0) + 1

            # First loop round
            loop_rounds = [r for s, r in cl.depth.items() if s.has_loop]
            first_loop_round = min(loop_rounds) if loop_rounds else None

            # First oneLoop round
            one_loop_rounds = [
                r for s, r in cl.depth.items() if s.n == 1 and s.has_loop
            ]
            first_oneloop_round = min(one_loop_rounds) if one_loop_rounds else None

            summary_data[run_key] = {
                "total_results": len(cl.depth),
                "by_round": {str(k): v for k, v in sorted(by_round.items())},
                "first_loop_round": first_loop_round,
                "first_oneloop_round": first_oneloop_round,
                "frontier_count": len(cl.frontier),
                "unexpanded_count": len(cl.unexpanded),
            }

    p_summary = out_dir / "summary.json"
    p_summary.write_text(json.dumps(summary_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_summary)

    # 2. Comparison with seventeenth
    comparison_data: dict[str, object] = {}
    for bra in (False, True):
        for sameness in (Sameness.ANCHORED, Sameness.FREE):
            cfg = f"bra_{bra}_{sameness.value}"
            start = given(bra, sameness)
            # Seventeenth A-replace (refusal without memory)
            seventeenth_rep = seventeenth_closure_replace(start, bound=3, rounds=4)
            # Problem 05 refusal memory
            p05_rep = closure(start, bound=3, rounds=4, enter_obstructed=False)
            # Seventeenth A-perform (perform immediately)
            seventeenth_perf = seventeenth_closure_perform(start, bound=3, rounds=4)

            # Check loop states reached
            sev_rep_loops = [s for s in seventeenth_rep.depth if s.loops]
            p05_loops = [s for s in p05_rep.depth if s.has_loop]
            sev_perf_loops = [s for s in seventeenth_perf.depth if s.loops]

            # Round of oneLoop
            oneloop_sev_rep = None
            for replacement_state, r in seventeenth_rep.depth.items():
                if replacement_state.n == 1 and replacement_state.loops:
                    oneloop_sev_rep = r
                    break

            oneloop_p05 = None
            for memory_state, r in p05_rep.depth.items():
                if memory_state.n == 1 and memory_state.has_loop:
                    oneloop_p05 = r
                    break

            oneloop_sev_perf = None
            for performed_state, r in seventeenth_perf.depth.items():
                if performed_state.n == 1 and performed_state.loops:
                    oneloop_sev_perf = r
                    break

            comparison_data[cfg] = {
                "seventeenth_replace": {
                    "total_states": len(seventeenth_rep.depth),
                    "loop_states_count": len(sev_rep_loops),
                    "oneloop_round": oneloop_sev_rep,
                },
                "problem05_refusal_memory": {
                    "total_states": len(p05_rep.depth),
                    "loop_states_count": len(p05_loops),
                    "oneloop_round": oneloop_p05,
                },
                "seventeenth_perform": {
                    "total_states": len(seventeenth_perf.depth),
                    "loop_states_count": len(sev_perf_loops),
                    "oneloop_round": oneloop_sev_perf,
                },
                "falsifier_agrees_with_seventeenth": (
                    len(p05_loops) == len(sev_rep_loops) and oneloop_p05 == oneloop_sev_rep
                ),
            }

    p_comp = out_dir / "comparison.json"
    p_comp.write_text(json.dumps(comparison_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_comp)

    # 3. Frontier and unexpanded details
    frontier_data: dict[str, object] = {}
    for run_key, cl in runs.items():
        frontier_data[run_key] = {
            "frontier_sample": list(cl.frontier[:10]),
            "frontier_total": len(cl.frontier),
            "unexpanded_sample": list(cl.unexpanded[:10]),
            "unexpanded_total": len(cl.unexpanded),
        }
    p_frontier = out_dir / "frontier.json"
    p_frontier.write_text(json.dumps(frontier_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_frontier)

    # 4. Independent census counts
    census_data: dict[str, object] = {
        "anchored_bound_1": len(independent_census(bound=1, sameness=Sameness.ANCHORED)),
        "anchored_bound_2": len(independent_census(bound=2, sameness=Sameness.ANCHORED)),
        "free_bound_1": len(independent_census(bound=1, sameness=Sameness.FREE)),
        "free_bound_2": len(independent_census(bound=2, sameness=Sameness.FREE)),
        "loopfree_anchored_bound_1": len(loopfree_census(bound=1, sameness=Sameness.ANCHORED)),
        "loopfree_anchored_bound_2": len(loopfree_census(bound=2, sameness=Sameness.ANCHORED)),
        "loopfree_free_bound_1": len(loopfree_census(bound=1, sameness=Sameness.FREE)),
        "loopfree_free_bound_2": len(loopfree_census(bound=2, sameness=Sameness.FREE)),
    }
    p_census = out_dir / "census.json"
    p_census.write_text(json.dumps(census_data, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    written.append(p_census)

    # 5. MANIFEST.sha256
    lines: list[str] = []
    for name in sorted(EVIDENCE_FILES):
        p = out_dir / name
        digest = compute_sha256(p)
        lines.append(f"{digest}  {name}\n")
    p_manifest = out_dir / "MANIFEST.sha256"
    p_manifest.write_text("".join(lines), encoding="utf-8", newline="\n")
    written.append(p_manifest)

    return written


def verify_check(evidence_dir: Path) -> bool:
    """Verify evidence against a fresh regeneration in a temporary directory."""
    temp_dir = Path(tempfile.mkdtemp(prefix="evidence_check_"))
    try:
        generate_all_evidence(temp_dir)
        for name in EVIDENCE_FILES + ("MANIFEST.sha256",):
            orig_path = evidence_dir / name
            gen_path = temp_dir / name
            if not orig_path.exists():
                print(f"Check failed: missing expected file {orig_path}")
                return False
            if compute_sha256(orig_path) != compute_sha256(gen_path):
                print(f"Check failed: hash mismatch on {name}")
                return False
        return True
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=HERE / "evidence",
        help="Directory to write evidence files",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Check byte-identical regeneration against committed evidence",
    )
    args = parser.parse_args(argv)

    if args.check:
        ok = verify_check(args.out)
        if ok:
            print("Evidence check passed: byte-identical regeneration verified.")
            return 0
        else:
            print("Evidence check failed.")
            return 1

    generate_all_evidence(args.out)
    print(f"Generated {len(EVIDENCE_FILES) + 1} evidence files in {args.out}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
