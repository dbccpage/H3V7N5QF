"""Scratch (not evidence): which check disagrees at a very small plan."""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, "code")

from twentyfourth.evidence import Plan, write_all  # noqa: E402

SMALL = Plan(bound=2, rounds=3, deep_bound=2, deep_rounds=2, two_term_rounds=3, log_bound=2, log_rounds=1,
             reach_bound=2, reach_rounds=2, same_small=1, same_large=1, readings_bound=2, readings_rounds=2,
             layers_upto=3, closed_form_upto=3, points_upto=2)
with tempfile.TemporaryDirectory() as tmp:
    s = write_all(Path(tmp), SMALL)
    d = s["disagreements"]
    assert isinstance(d, dict)
    for k, v in d.items():
        if v:
            print(k, v[:5])
