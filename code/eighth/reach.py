"""Reachability between results under the eighth seed: the names on the `r` part decide.

Derived (paper, `lean4/Eighth/Reach.lean`)
    From a well-formed state whose names, if one term, are one term in the
    target, the target is reached: remove every `s` assertion, follow the
    sixth's path on the `r` part (remove everything, identify every other
    term into the named one, move the names, add what the target's `r` part
    has — with nothing in `s` all along, since an identification keeps an
    empty relation empty), then add the target's `s` assertions.  Once the
    names are one term they stay one term.  So `t` is reachable from `s`
    exactly when the sixth's criterion holds for the `r` parts; the `s` parts
    impose nothing.  Under FREE every result reaches every result.

Cited from the sixth derivation (`sixth.reach`) and re-checked
    `reachable` is the sixth's criterion; applied to the `r` parts it is this
    seed's criterion, and it survives as such (the `s` part enters nowhere).
    `reach_graph` and `reachable_in_graph` are written again for this
    package's explorations.
"""

from __future__ import annotations

from sixth.reach import reachable as reachable_part

from eighth.changes import changes, perform
from eighth.explore import Exploration, order
from eighth.state import DState, canonical

__all__ = ["mutual", "reach_graph", "reachable", "reachable_by_search", "reachable_in_graph", "reachable_part"]


def reachable(s: DState, t: DState) -> bool:
    """Is `t` reachable from `s` by changes of the eighth seed (both with terms)?"""
    return reachable_part(s.r_part(), t.r_part())


def mutual(s: DState, t: DState) -> bool:
    """Do `s` and `t` reach each other?"""
    return reachable(s, t) and reachable(t, s)


def reachable_by_search(s: DState, bound: int, rounds: int) -> set[DState]:
    """Every result (least writing) reached from `s` within `bound` terms and `rounds` changes."""
    root = canonical(s)
    seen = {root}
    wave = [root]
    for _ in range(rounds):
        found = []
        for state in wave:
            for change in changes(state):
                out = perform(state, change)
                if out.n > bound:
                    continue
                out = canonical(out)
                if out not in seen:
                    seen.add(out)
                    found.append(out)
        wave = found
    return seen


def reach_graph(expl: Exploration) -> dict[DState, tuple[DState, ...]]:
    """The changes among the results of `expl`, as a graph (outcomes outside it dropped)."""
    inside = expl.depth
    graph: dict[DState, tuple[DState, ...]] = {}
    for state in sorted(inside, key=order):
        outs: list[DState] = []
        for change in changes(state):
            out = perform(state, change)
            if out.n > expl.bound:
                continue
            out = canonical(out)
            if out in inside and out not in outs:
                outs.append(out)
        graph[state] = tuple(outs)
    return graph


def reachable_in_graph(graph: dict[DState, tuple[DState, ...]], s: DState) -> set[DState]:
    """Every node of `graph` reached from `s` along its edges (`s` included)."""
    seen = {s}
    wave = [s]
    while wave:
        found = []
        for state in wave:
            for out in graph[state]:
                if out not in seen:
                    seen.add(out)
                    found.append(out)
        wave = found
    return seen
