"""Re-run every derivation's `--check`, earlier ones and this one (research helper; the outcome is recorded
in the change log and the commit message).

Run from the repository root: `python research/twentyfifth/check_earlier.py [SCRIPT ...]`.
"""

from __future__ import annotations

import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPTS = [
    "generate.py",
    "generate_second.py",
    "generate_third.py",
    "generate_fourth.py",
    "generate_fifth.py",
    "generate_sixth.py",
    "generate_seventh.py",
    "generate_eighth.py",
    "generate_ninth.py",
    "generate_tenth.py",
    "generate_eleventh.py",
    "generate_twelfth.py",
    "generate_thirteenth.py",
    "generate_fourteenth.py",
    "generate_fifteenth.py",
    "generate_sixteenth.py",
    "run_seventeenth.py",
    "run_eighteenth.py",
    "run_nineteenth.py",
    "run_twentieth.py",
    "run_twentyfirst.py",
    "run_twentysecond.py",
    "run_twentythird.py",
    "run_twentyfifth.py",
]
failed = 0
for script in sys.argv[1:] or SCRIPTS:
    t0 = time.perf_counter()
    done = subprocess.run(
        [sys.executable, str(ROOT / "code" / script), "--check"], cwd=ROOT, capture_output=True, text=True, check=False
    )
    tail = (done.stdout + done.stderr).strip().splitlines()[-1:] or [""]
    print(f"{script}: exit {done.returncode} ({time.perf_counter() - t0:.0f}s) {tail[0]}", flush=True)
    failed += done.returncode != 0
print(f"failed: {failed}")
