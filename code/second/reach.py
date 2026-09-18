"""Reachability between results: the carrying-map criterion.

Derived (paper, `lean4/Second/Carry.lean` and `Cost.lean`)
    A sequence of changes from `s` to `t` induces a map `q` of the terms of
    `s` to the terms of `t` that carries every asserted `xry` to an asserted
    `q(x) r q(y)` and the names to the names (identification replaces terms,
    additions keep everything).  Conversely such a map gives a sequence of
    changes: identify the terms that `q` merges (unobstructed, since `t` is
    legal), write the rest as `q` writes them, add the missing terms, add the
    missing assertions.  So `t` is reachable from `s` exactly when a carrying
    map exists, and the sequence never has more terms than `s` or `t` has.

Computed
    `carrying_map` searches for such a map by backtracking; `reachable_by_search`
    follows the changes breadth-first within a bound.  `second.evidence`
    compares the two on every pair of results within a small bound.
"""

from __future__ import annotations

from collections.abc import Sequence

from xry.state import State, canonical

from second.changes import changes, obstruction, perform

__all__ = ["carries", "carrying_map", "reachable", "reachable_by_search"]


def carries(q: Sequence[int], s: State, t: State) -> bool:
    """Does `q` carry `s` to `t`: assertions to assertions, names to names?"""
    if len(q) != s.n or any(not 0 <= v < t.n for v in q):
        return False
    if (s.names is None) != (t.names is None):
        return False
    if s.names is not None and t.names is not None:
        if (q[s.names[0]], q[s.names[1]]) != t.names:
            return False
    return all(t.has(q[x], q[y]) for x, y in s.pairs)


def carrying_map(s: State, t: State) -> tuple[int, ...] | None:
    """A map of the terms of `s` to those of `t` carrying `s` to `t`, or `None`.

    Backtracking over the terms of `s` in order; the names are placed first.
    """
    if (s.names is None) != (t.names is None):
        raise ValueError("both states carry names, or neither")
    n = s.n
    image = [-1] * n
    if s.names is not None and t.names is not None:
        (a, b), (ta, tb) = s.names, t.names
        image[a] = ta
        if image[b] not in (-1, tb):
            return None
        image[b] = tb
    free = [x for x in range(n) if image[x] < 0]

    def fits(x: int, v: int) -> bool:
        """Every assertion between `x` and an already placed term is carried."""
        for u in range(n):
            w = image[u]
            if w < 0:
                continue
            if s.has(x, u) and not t.has(v, w):
                return False
            if s.has(u, x) and not t.has(w, v):
                return False
        return True

    def place(i: int) -> bool:
        if i == len(free):
            return True
        x = free[i]
        for v in range(t.n):
            if fits(x, v):
                image[x] = v
                if place(i + 1):
                    return True
                image[x] = -1
        return False

    if place(0) and carries(image, s, t):
        return tuple(image)
    return None


def reachable(s: State, t: State) -> bool:
    """Is `t` reachable from `s` by changes of the second seed?"""
    return carrying_map(s, t) is not None


def reachable_by_search(s: State, bound: int) -> set[State]:
    """Every result (least writing) reached from `s` within `bound` terms."""
    root = canonical(s)
    seen = {root}
    wave = [root]
    while wave:
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
