"""Reachability between results of the tenth seed.

Cited from the ninth derivation (`ninth.reach`) and re-checked
    Under C-L1 a result reaches another exactly when the other has a term or
    the first is empty: leftover is not in the state, so the criterion
    survives and is imported.

Derived
    Under C-L2 tagged reachability follows the tagged changes: a tag does
    not block later changes of either relation, but two tags on one ninth
    state are different results.
"""

from __future__ import annotations

from ninth.reach import reach_graph, reachable, reachable_eighth, reachable_in_graph, reachable_on_part

from tenth.explore import TaggedExploration
from tenth.state import Tagged

__all__ = [
    "reach_graph",
    "reachable",
    "reachable_eighth",
    "reachable_in_graph",
    "reachable_on_part",
    "tagged_reachable",
]


def tagged_reachable(expl: TaggedExploration, start: Tagged, end: Tagged) -> bool:
    """Is `end` among the tagged results reached from `start` in this exploration?

    The exploration is from the empty beginning; `start` must be that
    beginning for the recorded depths to apply.  Used as a witness that
    several tags on one ninth state are reached, not as a closed criterion.
    """
    del start
    return end in expl.depth
