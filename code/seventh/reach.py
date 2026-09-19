"""Reachability between results under the seventh seed: a term decides.

Derived (paper, `lean4/Seventh/Reach.lean`)
    From a well-formed state with a term every well-formed state with a term
    is reached: the sixth's path (remove everything, identify every other
    term into one, add what the target has), re-checked through the naming
    map — put both names on a term of the start and on a term of the
    target, and the sixth's criterion (`reach6_of_names`) applies with
    nothing to check.  From the empty state every well-formed state is
    reached by additions.  Every change on a state with a term leaves a
    state with a term, so no state with a term reaches the empty state.  So
    `t` is reachable from `s` exactly when `t` has a term or `s` is empty:
    mutual among the states with a term, one-way out of the empty state.

Cited from the sixth derivation (`sixth.reach`) and re-checked
    The sixth's criterion without names (FREE) says "always" for two states
    with a term; it survives there and is imported as `reachable_sixth` for
    the comparison on every pair of results with a term (`seventh.evidence`).
    It has no clause for the empty state, which the sixth never reaches.  The
    sixth's `reach_graph` and `reachable_in_graph` are written again for
    this package's explorations (the same changes, the same least writings).

Computed
    `reachable` is the criterion; `reach_graph` and `reachable_in_graph`
    follow the changes among the results of an exploration, and
    `seventh.evidence` compares the two on every pair of results within a
    small bound.
"""

from __future__ import annotations

from sixth.reach import reachable as reachable_sixth

from seventh.changes import changes, perform
from seventh.explore import Exploration, order
from seventh.state import MState, canonical, has_term

__all__ = ["mutual", "reach_graph", "reachable", "reachable_by_search", "reachable_in_graph", "reachable_sixth"]


def reachable(s: MState, t: MState) -> bool:
    """Is `t` reachable from `s` by changes of the seventh seed (both well formed, no names)?"""
    if s.names is not None or t.names is not None:
        raise ValueError("a state of the seventh seed carries no names")
    return not has_term(s) or has_term(t)


def mutual(s: MState, t: MState) -> bool:
    """Do `s` and `t` reach each other?"""
    return reachable(s, t) and reachable(t, s)


def reachable_by_search(s: MState, bound: int, rounds: int) -> set[MState]:
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


def reach_graph(expl: Exploration) -> dict[MState, tuple[MState, ...]]:
    """The changes among the results of `expl`, as a graph.

    Every result (the last round's included) gets every change whose outcome
    is a result of the exploration; outcomes outside it are dropped, so every
    path in the graph is a sequence of changes.
    """
    inside = expl.depth
    graph: dict[MState, tuple[MState, ...]] = {}
    for state in sorted(inside, key=order):
        outs: list[MState] = []
        for change in changes(state):
            out = perform(state, change)
            if out.n > expl.bound:
                continue
            out = canonical(out)
            if out in inside and out not in outs:
                outs.append(out)
        graph[state] = tuple(outs)
    return graph


def reachable_in_graph(graph: dict[MState, tuple[MState, ...]], s: MState) -> set[MState]:
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
