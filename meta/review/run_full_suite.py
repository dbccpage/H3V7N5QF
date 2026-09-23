"""Run the full native gate/evidence/report suite and save exact local receipts.

This does not use the network. It runs all baseline commands on the current
tree, and adds the citation gate if that shared repair exists on the branch.
It never writes to the immutable `baseline/` receipt directory.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from run_baseline import ROOT, commands


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
    if (ROOT / "ci" / "check_axiom_citations.py").is_file():
        position = next(i for i, (name, _) in enumerate(sequence) if name == "lean_build")
        sequence.insert(position, ("axiom_citations", [sys.executable, "ci/check_axiom_citations.py"]))
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
