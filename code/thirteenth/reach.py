"""Reachability between results of the thirteenth seed.

Cited from the ninth derivation (`ninth.reach`) and re-checked
    Under C-C1 a result reaches another exactly when the other has a term or
    the first is empty: a coarser writing is not in the state, so the
    criterion survives and is imported.  The coarser writing has a term
    exactly when the finer state has a term, so the criterion descends.

Derived
    Under C-C2 coarser reachability is the seventh's has-a-term criterion
    on the coarser writing.
"""

from __future__ import annotations

from ninth.reach import reach_graph, reachable, reachable_eighth, reachable_in_graph, reachable_on_part

from thirteenth.explore import CoarseExploration
from thirteenth.state import Coarse

__all__ = [
    "coarse_reachable",
    "reach_graph",
    "reachable",
    "reachable_eighth",
    "reachable_in_graph",
    "reachable_on_part",
]


def coarse_reachable(expl: CoarseExploration, start: Coarse, end: Coarse) -> bool:
    """Is `end` among the coarser results reached from `start` in this exploration?

    The exploration is from the empty beginning; `start` must be that
    beginning for the coarser depths to apply.
    """
    del start
    return end in expl.depth
