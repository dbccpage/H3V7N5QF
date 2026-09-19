"""Reachability between results under the sixth seed: the names decide, as under the fifth.

Derived (paper, `lean4/Sixth/Reach.lean`)
    From a well-formed state with `a ≠ b` every well-formed state with at
    least one term is reached, with its names anywhere: remove every
    assertion, identify every other term into `a` (no identification is
    barred now), move the names onto the target's named terms, add the missing
    terms, raise the multiplicities — `xrx` like any other pair.  From a state
    with `a = b` the names stay one term.  So `t` is reachable from `s`
    exactly when: the names, if one term in `s`, are one term in `t`
    (ANCHORED); always (FREE).  Reachability is mutual within these two
    classes and one-way from the first to the second.

Cited from the fifth derivation (`fifth.reach`) and re-checked
    The criterion is the fifth's statement with "legal" dropped from both
    states; its proof is re-done without legality.  `fifth.reach.reachable`
    is imported as `reachable_fifth` and compared with this module's on every
    pair of the fifth's results (`sixth.evidence`): they must agree there.
    The fifth's `reach_graph` and `reachable_by_search` filtered obstructed
    changes out; they are written again without the filter.

Computed
    `reachable` is the criterion; `reach_graph` and `reachable_in_graph`
    follow the changes among the results of an exploration, and
    `sixth.evidence` compares the two on every pair of results within a
    small bound.
"""

from __future__ import annotations

from fifth.reach import reachable as reachable_fifth

from sixth.changes import changes, perform
from sixth.explore import Exploration, order
from sixth.state import MState, canonical, names_one_term

__all__ = [
    "mutual",
    "reach_graph",
    "reachable",
    "reachable_by_search",
    "reachable_fifth",
    "reachable_in_graph",
]


def reachable(s: MState, t: MState) -> bool:
    """Is `t` reachable from `s` by changes of the sixth seed (both with terms)?"""
    if (s.names is None) != (t.names is None):
        raise ValueError("both states carry names, or neither")
    if s.n < 1 or t.n < 1:
        return False
    return not names_one_term(s) or names_one_term(t)


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
