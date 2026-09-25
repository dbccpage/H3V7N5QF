"""Evidence generation and verification for Problem 04 (Written Refusal).

Generates `summary.json` and `MANIFEST.sha256` under the evidence directory.
Supports `--check` to verify byte-identical regeneration against a temporary directory.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from collections.abc import Sequence
from pathlib import Path

# Ensure derivation directory is on sys.path
HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:  # pragma: no cover - direct script invocation
    sys.path.insert(0, str(HERE))

# Ensure repo code/ directory is on sys.path
ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:  # pragma: no cover - direct script invocation
    sys.path.insert(0, str(ROOT / "code"))

from model import (  # noqa: E402
    aut_size,
    compare_with_eighteenth,
    compare_with_twentyfirst,
    explore_written_refusal,
    orbit_size,
    orbit_splits_factorial,
    same_written,
    verify_census,
)
from xry.evidence import compare_evidence, write_manifest  # noqa: E402
from xry.state import Sameness, State, canonical, given, rewrite  # noqa: E402


def measure_run(bra: bool, sameness: Sameness, bound: int, rounds: int) -> dict[str, object]:
    """Gather metrics and differential checks for one configuration."""
    start = given(bra, sameness)
    expl = explore_written_refusal(start, bound, rounds)
    comp18 = compare_with_eighteenth(bra, sameness, bound, rounds)
    comp21 = compare_with_twentyfirst(bra, sameness, bound, rounds)
    census_ok = verify_census(expl, sameness)

    # Check orbit formula for every reached state
    orbit_fails = [s.key() for s in expl.depth if not orbit_splits_factorial(s)]

    return {
        "bra": bra,
        "sameness": sameness.value,
        "written_results": len(expl.depth),
        "new_per_round": expl.new_per_round,
        "total_refusals": expl.total_refusals,
        "refusals_per_round": expl.refusals_per_round,
        "frontier_exits": len(expl.frontier),
        "eighteenth_depth_matches": comp18["depth_matches"],
        "eighteenth_waves_match": comp18["waves_match"],
        "eighteenth_disagreements": comp18["disagreements"],
        "eighteenth_round_mismatches": comp18["round_mismatches"],
        "twentyfirst_quotient_matches": comp21["quotient_matches"],
        "quotient_classes_count": comp21["quotient_classes_count"],
        "splitting_classes_count": comp21["splitting_classes_count"],
        "max_fiber_size": comp21["max_fiber_size"],
        "census_matches": census_ok,
        "orbit_formula_fails": orbit_fails,
    }


def write_all(out: Path, bound: int = 3, rounds: int = 12) -> dict[str, object]:
    """Generate all evidence files and write SHA-256 manifest."""
    out.mkdir(parents=True, exist_ok=True)
    start_anchored = given(False, Sameness.ANCHORED)
    swapped_anchored = rewrite(start_anchored, (1, 0))

    runs = [
        measure_run(bra, sameness, bound, rounds)
        for bra in (False, True)
        for sameness in (Sameness.ANCHORED, Sameness.FREE)
    ]

    all_18_match = all(bool(r["eighteenth_depth_matches"]) and bool(r["eighteenth_waves_match"]) for r in runs)
    all_21_quotient_match = all(bool(r["twentyfirst_quotient_matches"]) for r in runs)
    all_census_match = all(bool(r["census_matches"]) for r in runs)
    all_orbit_ok = all(len(r["orbit_formula_fails"]) == 0 for r in runs)  # type: ignore[arg-type]

    summary: dict[str, object] = {
        "problem": "04-written-refusal",
        "bound": bound,
        "rounds": rounds,
        "given_orbit": orbit_size(start_anchored),
        "given_aut": aut_size(start_anchored),
        "given_equals_its_swap": same_written(start_anchored, swapped_anchored),
        "base_calls_them_the_same": canonical(State(start_anchored.n, start_anchored.mask, None))
        == canonical(State(swapped_anchored.n, swapped_anchored.mask, None)),
        "all_eighteenth_closures_match": all_18_match,
        "all_twentyfirst_quotients_match": all_21_quotient_match,
        "all_censuses_match": all_census_match,
        "all_orbit_formulas_pass": all_orbit_ok,
        "hypothesis_holds": not all_18_match,
        "falsifier_holds": all_18_match,
        "resolution": (
            "FALSIFIED: The written refusal closure is exactly the eighteenth's closure at every round. "
            "Written sameness and refusal do not interact beyond a quotient of the same closure."
        ),
        "runs": runs,
    }

    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(out)
    return summary


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point for evidence generation and checking."""
    parser = argparse.ArgumentParser(prog="evidence", description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "evidence")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bound", type=int, default=3)
    parser.add_argument("--rounds", type=int, default=12)
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.check:
        if not args.out.is_dir():
            print("missing evidence directory")
            return 1
        with tempfile.TemporaryDirectory() as tmp:
            fresh = Path(tmp) / "fresh"
            write_all(fresh, args.bound, args.rounds)
            diffs = compare_evidence(args.out, fresh)
        if diffs:
            for line in diffs:
                print(line)
            return 1
        print("evidence matches a fresh regeneration")
        return 0

    write_all(args.out, args.bound, args.rounds)
    print(f"wrote evidence to {args.out}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
