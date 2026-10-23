"""Run the full native gate/evidence/report suite and save exact local receipts.

It extends the historical baseline plan with the current evidence and report
launchers and both pinned Lean roots. It adds no check or threshold. Lean must
already be available offline; the child tools are not network-sandboxed here.
It never writes to the immutable `baseline/` receipt directory.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from run_baseline import ROOT, commands as baseline_commands


def commands() -> list[tuple[str, list[str]]]:
    """The current plan; leave the historical baseline recipe unchanged."""
    sequence = baseline_commands()
    known = {name for name, _ in sequence}
    for pattern, prefix in (("generate_*.py", "generate_"), ("run_*.py", "run_")):
        for path in sorted((ROOT / "code").glob(pattern)):
            name = "evidence_" + path.stem.removeprefix(prefix)
            if name not in known:
                position = next(i for i, (label, _) in enumerate(sequence) if label == "axioms_base")
                sequence.insert(position, (name, [sys.executable, path.relative_to(ROOT).as_posix(), "--check"]))
                known.add(name)
    for path in sorted((ROOT / "code").glob("lean_report_*.py")):
        name = "axioms_" + path.stem.removeprefix("lean_report_")
        if name not in known:
            position = next(i for i, (label, _) in enumerate(sequence) if label == "git_status")
            sequence.insert(position, (name, [sys.executable, path.relative_to(ROOT).as_posix()]))
            known.add(name)
    position = next(i for i, (name, _) in enumerate(sequence) if name == "lean_build")
    builds = []
    for root, label in (("lean4", "lean_build"), ("lean4_core", "lean_core_build")):
        pin = (ROOT / root / "lean-toolchain").read_text(encoding="utf-8").strip()
        builds.append((label, ["lake", "+" + pin, "-d", root, "build"]))
    sequence[position:position + 1] = builds
    sequence.insert(position, ("axiom_citations", [sys.executable, "ci/check_axiom_citations.py"]))
    return sequence


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    )
    return result.stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    if out == ROOT / "meta" / "review" / "baseline":
        raise ValueError("the baseline receipts are immutable")
    out.mkdir(parents=True, exist_ok=True)
    sequence = commands()
    summary: dict[str, object] = {
        "branch": git("branch", "--show-current"),
        "head": git("rev-parse", "HEAD"),
        "started_utc": now(),
        "commands": [],
    }
    records: list[dict[str, object]] = []
    for index, (name, command) in enumerate(sequence, 1):
        log_name = f"{index:02d}-{name}.log"
        print(f"START {index:02d} {name}", flush=True)
        started = now()
        with (out / log_name).open("wb") as log:
            try:
                done = subprocess.run(
                    command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                    check=False,
                )
                exit_code = done.returncode
            except OSError as error:
                log.write(f"Unable to start: {error}\n".encode("utf-8"))
                exit_code = 127
        records.append({
            "name": name, "command": command, "started_utc": started,
            "finished_utc": now(), "exit_code": exit_code, "log": log_name,
        })
        summary["commands"] = records
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print(f"END   {index:02d} {name}: {exit_code}", flush=True)
    summary["finished_utc"] = now()
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    return 0 if all(record["exit_code"] == 0 for record in records) else 1


if __name__ == "__main__":
    raise SystemExit(main())
