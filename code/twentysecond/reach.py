"""Reachability between results under the twenty-second seed.

Derived (paper; `lean4_core/Twentysecond/Reach.lean`, `reach_criterion`)
    A result reaches another exactly when the other has a term or the first
    is the empty state — the ninth's criterion (`paper/ninth/`, D8),
    re-proved for this seed's results: remove every assertion, identify the
    terms down to one, add terms, add the plain state of the target.  No
    state along that path has more terms, or a larger cost, than the larger
    of the two ends, so the search among the results of one exploration
    (`reach_graph`) decides every pair within its bound.

Cited from the ninth derivation (`ninth.reach`) and re-checked
    `reachable` is the ninth's criterion with the same wording; it is written
    again here for results (the least writings of plain states) and compared
    with a search, not imported.
"""

from __future__ import annotations

from twentysecond.changes import perform, result_changes
from twentysecond.explore import Exploration, order
from twentysecond.state import DState, result_of

__all__ = ["reach_graph", "reachable", "reachable_in_graph"]


def reachable(s: DState, t: DState) -> bool:
    """Is the result `t` reachable from the result `s`?  Exactly when `t` has a term or `s` is empty."""
    return t.n >= 1 or s.n == 0


def reach_graph(expl: Exploration) -> dict[DState, tuple[DState, ...]]:
    """The explored results one change away from each explored result (its changes performed, whatever
    its round)."""
    edges: dict[DState, set[DState]] = {s: set() for s in expl.depth}
    for state in expl.depth:
        for change in result_changes(state):
            raw = perform(state, change)
            if raw.n <= expl.bound:
                out = result_of(raw)
                if out in expl.depth:
                    edges[state].add(out)
    return {s: tuple(sorted(v, key=order)) for s, v in edges.items()}


def reachable_in_graph(graph: dict[DState, tuple[DState, ...]], s: DState) -> set[DState]:
    """Every result reached from `s` along the graph, `s` included."""
    seen = {s}
    todo = [s]
    while todo:
        cur = todo.pop()
        for nxt in graph.get(cur, ()):
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return seen
