"""Reachability between results under the twenty-fifth seed.

Derived (paper, D12; `lean4_core/Twentyfifth/Reach.lean`, `reach25_criterion`)
    A result reaches another exactly when the other has a term or the first is
    the empty state: remove every assertion, identify the terms down to one —
    a state with one term has nothing filled, so every filled triple is gone —
    add terms, add the other's plain part, fill its triples.  Every state along
    that path has no more terms, and no larger `phi` plus filled triples, than
    the larger of the two ends, so a search among the states of one
    exploration decides every pair within its bound (`reached_by_search`).

Chosen here
    The search runs on the explored states (plain, least writing): the
    twenty-second's sameness with the filled triples kept is respected by every
    change (the outcomes of one change on two such states are one such state),
    so reachability between them is reachability between states.
"""

from __future__ import annotations

from twentyfifth.explore import Grouped
from twentyfifth.state import FState, Mark, canonical_state, changes, perform, plain_state, result_mark

__all__ = ["reachable", "reached_by_search", "search_graph"]


def reachable(s: FState, t: FState) -> bool:
    """Does the result of `s` reach the result of `t`?  Exactly when `t` has a term or `s` is empty."""
    return t.n >= 1 or s.n == 0


def search_graph(grouped: Grouped) -> dict[FState, tuple[FState, ...]]:
    """The explored states one change away from each explored state (every change performed, the last round's
    included)."""
    depth = grouped.states.depth
    graph: dict[FState, tuple[FState, ...]] = {}
    for fs in depth:
        outs: list[FState] = []
        for change in changes(fs):
            raw = perform(fs, change)
            if raw.n > grouped.bound:
                continue
            out = canonical_state(plain_state(raw))
            if out in depth:
                outs.append(out)
        graph[fs] = tuple(outs)
    return graph


def reached_by_search(grouped: Grouped, graph: dict[FState, tuple[FState, ...]], mark: Mark) -> set[Mark]:
    """The results reached from any state of the result `mark`, along the explored states, itself included."""
    seen: set[FState] = set(grouped.members[mark])
    todo = list(seen)
    while todo:
        cur = todo.pop()
        for nxt in graph[cur]:
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return {result_mark(s) for s in seen}
