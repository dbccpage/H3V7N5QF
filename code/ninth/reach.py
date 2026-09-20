"""Reachability between results under the ninth seed: a term decides, whatever either relation says.

Derived (paper, `lean4/Ninth/Reach.lean`)
    From a well-formed state with a term every well-formed state with a term
    is reached: the eighth's path (clear `s`, the sixth's path on the `r`
    part, add the target's `s` assertions), re-checked through the naming
    map — put both names on a term of the start and on a term of the
    target, and the eighth's criterion (`reach8_of_names`) applies with
    nothing to check.  From the empty state every well-formed state is
    reached by additions.  Every change on a state with a term leaves a
    state with a term, so no state with a term reaches the empty state.  So
    `t` is reachable from `s` exactly when `t` has a term or `s` is empty:
    mutual among the states with a term, one-way out of the empty state.
    The eighth's "the `s` part imposes nothing" survives, and so does its
    mirror: the `r` part imposes nothing either, there being no names left
    for it to impose through; the criterion reads the terms the two relations
    share.

Cited from the seventh and eighth derivations (`seventh.reach`,
`eighth.reach`) and re-checked
    The seventh's criterion on a one-relation state ("has a term, or the
    start is empty") applied to either part is this seed's criterion, since
    the parts share their terms; it is imported as `reachable_part` and
    compared on both parts in `ninth.evidence`.  The eighth's criterion
    without names says "always" for two states with a term; it survives
    there and is imported as `reachable_eighth` for the comparison on every
    pair of results with a term.  Neither has a clause for the empty state
    that the other seed reaches — the seventh's does, the eighth's does not.
    `reach_graph` and `reachable_in_graph` are written again for this
    package's explorations (the same changes, the same least writings).

Computed
    `reachable` is the criterion; `reach_graph` and `reachable_in_graph`
    follow the changes among the results of an exploration, and
    `ninth.evidence` compares the two on every pair of results within a
    small bound.
"""

from __future__ import annotations

from eighth.reach import reachable as reachable_eighth
from seventh.reach import reachable as reachable_part

from ninth.changes import changes, perform
from ninth.explore import Exploration, order
from ninth.state import DState, canonical, has_term

__all__ = [
    "mutual",
    "reach_graph",
    "reachable",
    "reachable_by_search",
    "reachable_eighth",
    "reachable_in_graph",
    "reachable_on_part",
    "reachable_part",
]


def reachable(s: DState, t: DState) -> bool:
    """Is `t` reachable from `s` by changes of the ninth seed (both well formed, no names)?"""
    if s.names is not None or t.names is not None:
        raise ValueError("a state of the ninth seed carries no names")
    return not has_term(s) or has_term(t)


def reachable_on_part(s: DState, t: DState, rel: str) -> bool:
    """The seventh's criterion read on the `r` parts or the `s` parts (they share the terms)."""
    return reachable_part(s.part(rel), t.part(rel))


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
    """The changes among the results of `expl`, as a graph.

    Every result (the last round's included) gets every change whose outcome
    is a result of the exploration; outcomes outside it are dropped, so every
    path in the graph is a sequence of changes.
    """
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
