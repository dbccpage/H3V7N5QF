"""Scratch (not evidence): run the twenty-fifth mutation panel alone.

Run from the repository root: `python research/twentyfifth/try_bite.py`.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "code"))
sys.path.insert(0, str(ROOT / "ci"))

import check_mutation_bite as cmb  # noqa: E402

panel = cmb._twentyfifth()
problems = cmb.check_panel(panel)
print("problems:", problems or "none")
