"""Reachability between results of the twelfth seed.

Cited from the ninth derivation (`ninth.reach`) and re-checked
    Under C-M1 a result reaches another exactly when the other has a term or
    the first is empty: a record is not in the state, so the criterion
    survives and is imported.

Derived
    Under C-M2 recorded reachability follows the underlying state plus the
    attached record: two records on one ninth state are different results.
"""

from __future__ import annotations

from ninth.reach import reach_graph, reachable, reachable_eighth, reachable_in_graph, reachable_on_part

from twelfth.explore import RecordedExploration
from twelfth.state import Recorded

__all__ = [
    "reach_graph",
    "reachable",
    "reachable_eighth",
    "reachable_in_graph",
    "reachable_on_part",
    "recorded_reachable",
]


def recorded_reachable(expl: RecordedExploration, start: Recorded, end: Recorded) -> bool:
    """Is `end` among the recorded results reached from `start` in this exploration?

    The exploration is from the empty beginning; `start` must be that
    beginning for the recorded depths to apply.
    """
    del start
    return end in expl.depth
