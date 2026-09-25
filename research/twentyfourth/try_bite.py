"""Scratch (not evidence): the twenty-fourth panel of the mutation-bite gate alone."""

from __future__ import annotations

import sys

sys.path.insert(0, "ci")
sys.path.insert(0, "code")

import check_mutation_bite as cmb  # noqa: E402

panel = next(p for p in cmb.panels() if p.derivation == "twentyfourth")
problems = cmb.check_panel(panel)
print(problems or f"clean: {len(panel.cases)} fields bite")
