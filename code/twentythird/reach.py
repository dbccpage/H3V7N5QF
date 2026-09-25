"""Reachability between results under the twenty-third seed.

Chosen here (reading C-E)
    A result reaches another when some state of the first reaches, by changes
    performed on states, some state of the second.

Derived (paper, D9; `lean4_core/Twentythird/Reach.lean`, `reach3_criterion`)
    A result reaches another exactly when the other has a term or the first is
    the empty state: the twenty-second's criterion (22:D9) holds, since it is
    decided by the number of terms, which every clause of this seed's sameness
    keeps.  From any state of the first the path — remove every assertion,
    identify the terms down to one, add terms, add a state of the second
    asserting the fewest — never has more terms, or a larger size, than the
    larger of its two ends, so a search among the states of one exploration
    decides every pair within its bound.

Cited from the twenty-second derivation (`twentysecond.reach`) and re-checked
(no change)
    `reach_graph` (every change of every explored state, performed) and
    `reachable_in_graph` act on states and mention no sameness of results.
"""

from __future__ import annotations

from twentysecond.reach import reach_graph, reachable_in_graph

from twentythird.explore import Grouped
from twentythird.state import DState, Key, result_key

__all__ = ["reachable", "reached_by_search", "search_graph"]


def reachable(s: DState, t: DState) -> bool:
    """Does the result of `s` reach the result of `t`?  Exactly when `t` has a term or `s` is empty."""
    return t.n >= 1 or s.n == 0


def search_graph(grouped: Grouped) -> dict[DState, tuple[DState, ...]]:
    """The explored states one change away from each explored state."""
    return reach_graph(grouped.plain)


def reached_by_search(grouped: Grouped, graph: dict[DState, tuple[DState, ...]], key: Key) -> set[Key]:
    """The results reached from any state of the result `key`, along the explored states, itself included."""
    seen: set[DState] = set()
    for m in grouped.members[key]:
        if m not in seen:
            seen |= reachable_in_graph(graph, m)
    return {result_key(s) for s in seen}
