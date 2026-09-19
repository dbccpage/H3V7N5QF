"""Reachability between results under the fifth seed: the names decide.

Derived (paper, `lean4/Fifth/Reach.lean`)
    From a legal state with `a ≠ b` every legal state with at least one term
    is reached, with its names anywhere: remove every assertion, identify
    every other term into `a`, move the names onto the target's named terms
    (identifying a new term with an old one leaves the new one, carrying the
    name), add the missing terms, raise the multiplicities.  From a state with
    `a = b` the names stay one term (no change tells them apart), and every
    state with `a = b` is reached the same way.  So `t` is reachable from `s`
    exactly when: the names, if one term in `s`, are one term in `t`
    (ANCHORED); always (FREE).  Reachability is mutual within these two
    classes and one-way from the first to the second.

Cited from the fourth derivation (`fourth.reach`) and re-checked
    Containment with multiplicities (`fourth.reach.contains`, `embedding`) is
    still sufficient — additions are changes of the fifth seed — but no
    longer necessary: `fifth.evidence` counts the pairs reachable now that
    were not reachable then.  The fourth's criterion does not survive removal
    and identification.

Computed
    `reachable` is the criterion; `reach_graph` and `reachable_in_graph`
    follow the changes among the results of an exploration, and
    `fifth.evidence` compares the two on every pair of results within a
    small bound.
"""

from __future__ import annotations

from fourth.reach import contains, embedding
from fourth.reach import reachable as reachable_fourth

from fifth.changes import changes, obstruction, perform
from fifth.explore import Exploration, order
from fifth.state import MState, canonical, names_one_term

__all__ = [
    "contains",
    "embedding",
    "mutual",
    "reach_graph",
    "reachable",
    "reachable_by_search",
    "reachable_fourth",
    "reachable_in_graph",
]


def reachable(s: MState, t: MState) -> bool:
    """Is `t` reachable from `s` by changes of the fifth seed (both legal, with terms)?"""
    if (s.names is None) != (t.names is None):
        raise ValueError("both states carry names, or neither")
    if not (s.legal and t.legal and s.n >= 1 and t.n >= 1):
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
                if obstruction(state, change):
                    continue
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
    """The performed changes among the results of `expl`, as a graph.

    Every result (the last round's included) gets every unobstructed change
    whose outcome is a result of the exploration; outcomes outside it are
    dropped, so every path in the graph is a sequence of changes.
    """
    inside = expl.depth
    graph: dict[MState, tuple[MState, ...]] = {}
    for state in sorted(inside, key=order):
        outs: list[MState] = []
        for change in changes(state):
            if obstruction(state, change):
                continue
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
