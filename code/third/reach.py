"""Reachability between results under the third seed: containment.

Derived (paper, `lean4/Third/Contain.lean` and `Cost.lean`)
    A change adds and takes nothing away, so a sequence of changes from `s`
    to `t` leaves every term, every asserted `xry` and both names of `s` in
    place: `s` is contained in `t`.  Conversely a state that contains `s` is
    reached from `s` by adding the missing terms, then the missing
    assertions.  So `t` is reachable from `s` exactly when `s` is contained
    in `t`; the sequence never has more terms than `t`.  Up to sameness the
    containment is up to a rewriting of the terms of `s`: a one-to-one map of
    its terms into those of `t` that carries assertions to assertions and,
    with names, the names to the names — an embedding.  Reachability is
    one-way: two results reachable from each other are the same result.

Cited from the second derivation (`second.reach`) and re-checked
    An embedding is a carrying map that is one-to-one, so every pair
    reachable under the third seed is reachable under the second;
    `third.evidence` counts the pairs the second reaches and the third does
    not.

Computed
    `embedding` searches for such a map by backtracking; `reachable_by_search`
    follows the changes breadth-first within a bound.  `third.evidence`
    compares the two on every pair of results within a small bound.
"""

from __future__ import annotations

from collections.abc import Sequence

from second.reach import carries
from xry.state import State, canonical

from third.changes import changes, obstruction, perform

__all__ = ["carries", "contains", "embedding", "embeds", "reachable", "reachable_by_search"]


def contains(s: State, t: State) -> bool:
    """Is `s` contained in `t` as written: terms, assertions and names in place?"""
    if (s.names is None) != (t.names is None) or s.names != t.names:
        return False
    return s.n <= t.n and all(t.has(x, y) for x, y in s.pairs)


def embeds(q: Sequence[int], s: State, t: State) -> bool:
    """Does `q` embed `s` in `t`: one-to-one, carrying assertions and names?"""
    return len(set(q)) == len(q) and carries(q, s, t)


def embedding(s: State, t: State) -> tuple[int, ...] | None:
    """A one-to-one map of the terms of `s` into those of `t` embedding `s` in `t`, or `None`.

    Backtracking over the terms of `s` in order; the names are placed first.
    """
    if (s.names is None) != (t.names is None):
        raise ValueError("both states carry names, or neither")
    if s.n > t.n or s.m > t.m:
        return None
    n = s.n
    image = [-1] * n
    if s.names is not None and t.names is not None:
        (a, b), (ta, tb) = s.names, t.names
        image[a] = ta
        if image[b] not in (-1, tb) or (a != b and ta == tb):
            return None
        image[b] = tb
    free = [x for x in range(n) if image[x] < 0]

    def fits(x: int, v: int) -> bool:
        """`v` is unused, and every assertion between `x` and a placed term is carried."""
        for u in range(n):
            w = image[u]
            if w < 0:
                continue
            if w == v:
                return False
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

    if place(0) and embeds(image, s, t):
        return tuple(image)
    return None


def reachable(s: State, t: State) -> bool:
    """Is `t` reachable from `s` by changes of the third seed?"""
    return embedding(s, t) is not None


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
