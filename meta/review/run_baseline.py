"""Run every requested baseline gate and keep exact output and exit codes.

This runner changes no source file. Individual evidence reporters may refresh
their tracked reports; the final Git status records any such drift.
"""

from __future__ import annotations

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "meta" / "review" / "baseline"
ORDINALS = (
    "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth",
    "ninth", "tenth", "eleventh", "twelfth", "thirteenth", "fourteenth",
    "fifteenth", "sixteenth", "seventeenth", "eighteenth", "nineteenth",
    "twentieth", "twentyfirst",
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def commands() -> list[tuple[str, list[str]]]:
    py = sys.executable
    items = [
        ("pytest", [py, "-m", "pytest", "-n", "auto"]),
        ("coverage_gate", [py, "code/xry/gate.py", "coverage.json"]),
        ("mypy", [py, "-m", "mypy"]),
        ("prose_watchlist", [py, "ci/check_prose_watchlist.py"]),
        ("vacuous_checks", [py, "ci/check_vacuous_checks.py"]),
        ("definitional_citations", [py, "ci/check_definitional_citations.py"]),
        ("mutation_bite", [py, "ci/check_mutation_bite.py"]),
        ("lean_build", ["lake", "+leanprover/lean4:v4.33.1", "-d", "lean4", "build"]),
        ("evidence_base", [py, "code/generate.py", "--check"]),
    ]
    items.extend(
        (f"evidence_{name}", [py, f"code/generate_{name}.py", "--check"])
        for name in ORDINALS[:15]
    )
    items.extend(
        (f"evidence_{name}", [py, f"code/run_{name}.py", "--check"])
        for name in ORDINALS[15:]
    )
    items.append(("axioms_base", [py, "code/lean_report.py"]))
    items.extend(
        (f"axioms_{name}", [py, f"code/lean_report_{name}.py"])
        for name in ORDINALS
    )
    items.append(("git_status", ["git", "status", "--short", "--branch"]))
    return items


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    summary_path = OUT / "summary.json"
    summary: dict[str, object] = {
        "starting_main": "53b319a48f347b1a52e823ea7db46c79f8434c42",
        "plan_commit": "8f2c517",
        "started_utc": now(),
        "commands": [],
    }
    records: list[dict[str, object]] = []
    for index, (name, command) in enumerate(commands(), 1):
        log_name = f"{index:02d}-{name}.log"
        print(f"START {index:02d} {name}: {' '.join(command)}", flush=True)
        started = now()
        with (OUT / log_name).open("wb") as log:
            try:
                completed = subprocess.run(
                    command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                    check=False,
                )
                exit_code = completed.returncode
            except OSError as error:
                log.write(f"Unable to start: {error}\n".encode("utf-8"))
                exit_code = 127
        record: dict[str, object] = {
            "name": name, "command": command, "started_utc": started,
            "finished_utc": now(), "exit_code": exit_code, "log": log_name,
        }
        records.append(record)
        summary["commands"] = records
        summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print(f"END   {index:02d} {name}: exit {exit_code}", flush=True)
    return 0 if all(record["exit_code"] == 0 for record in records) else 1


if __name__ == "__main__":
    raise SystemExit(main())
