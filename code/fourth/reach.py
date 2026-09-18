"""Reachability between results under the fourth seed: containment with multiplicities.

Derived (paper, `lean4/Fourth/Contain.lean` and `Cost.lean`)
    A change adds a term or raises one multiplicity and takes nothing away,
    so a sequence of changes from `s` to `t` leaves every term and both
    names of `s` in place and every multiplicity of `s` the same or higher:
    `s` is contained in `t`.  Conversely a state that contains `s` is reached
    from `s` by adding the missing terms, then raising each multiplicity as
    often as it falls short.  So `t` is reachable from `s` exactly when `s`
    is contained in `t`; the sequence never has more terms than `t`.  Up to
    sameness the containment is up to a rewriting of the terms of `s`: a
    one-to-one map of its terms into those of `t` that carries names to
    names and each multiplicity to one at least as large — an embedding.
    Reachability is one-way: two results reachable from each other are the
    same result.

Cited from the third derivation (`third.reach`) and re-checked
    On states asserting nothing twice, "each multiplicity at most the
    image's" is "each asserted pair carried to an asserted pair", so the
    third's embeddings are the embeddings between the supports; the third's
    criterion survives on those states and `fourth.evidence` compares the two
    pair by pair.  The search (`embedding`) is written again for
    multiplicities.

Computed
    `embedding` searches for such a map by backtracking; `reachable_by_search`
    follows the changes breadth-first within a bound on terms and rounds.
    `fourth.evidence` compares the two on every pair of results within a
    small bound.
"""

from __future__ import annotations

from collections.abc import Sequence

from fourth.changes import changes, obstruction, perform
from fourth.state import MState, canonical

__all__ = ["contains", "embedding", "embeds", "reachable", "reachable_by_search"]


def contains(s: MState, t: MState) -> bool:
    """Is `s` contained in `t` as written: terms, names in place, every multiplicity not above `t`'s?"""
    if (s.names is None) != (t.names is None) or s.names != t.names:
        return False
    return s.n <= t.n and all(k <= t.mult_of(x, y) for x, y, k in s.counted)


def embeds(q: Sequence[int], s: MState, t: MState) -> bool:
    """Does `q` embed `s` in `t`: one-to-one, carrying names and every multiplicity to one at least as large?"""
    if len(q) != s.n or len(set(q)) != len(q) or any(not 0 <= v < t.n for v in q):
        return False
    if s.names is not None or t.names is not None:
        if s.names is None or t.names is None:
            return False
        if (q[s.names[0]], q[s.names[1]]) != t.names:
            return False
    return all(k <= t.mult_of(q[x], q[y]) for x, y, k in s.counted)


def embedding(s: MState, t: MState) -> tuple[int, ...] | None:
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
        if s.mult_of(x, x) > t.mult_of(v, v):
            return False
        for u in range(n):
            w = image[u]
            if w < 0:
                continue
            if w == v:
                return False
            if s.mult_of(x, u) > t.mult_of(v, w) or s.mult_of(u, x) > t.mult_of(w, v):
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


def reachable(s: MState, t: MState) -> bool:
    """Is `t` reachable from `s` by changes of the fourth seed?"""
    return embedding(s, t) is not None


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
