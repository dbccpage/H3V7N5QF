"""Reachability between results of the eleventh seed.

Cited from the ninth derivation (`ninth.reach`) and re-checked
    Under C-W1 a result reaches another exactly when the other has a term or
    the first is empty: a writing is not in the state, so the criterion
    survives and is imported.

Derived
    Under C-W2 labeled reachability follows the underlying state: a writing
    does not block later changes of either relation, but two writings on one
    ninth state are different results.
"""

from __future__ import annotations

from ninth.reach import reach_graph, reachable, reachable_eighth, reachable_in_graph, reachable_on_part

from eleventh.explore import LabeledExploration
from eleventh.state import Labeled

__all__ = [
    "labeled_reachable",
    "reach_graph",
    "reachable",
    "reachable_eighth",
    "reachable_in_graph",
    "reachable_on_part",
]


def labeled_reachable(expl: LabeledExploration, start: Labeled, end: Labeled) -> bool:
    """Is `end` among the labeled results reached from `start` in this exploration?

    The exploration is from the empty beginning; `start` must be that
    beginning for the recorded depths to apply.  Used as a witness that
    several writings on one ninth state are reached, not as a closed
    criterion.
    """
    del start
    return end in expl.depth
