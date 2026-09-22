"""Writings of a state's terms, determination, and coarser writings (eleventh seed).

Given by the eleventh seed
    A writing of terms may give two terms the same letter while they remain
    two terms.  Assertions are read from the writing.  If two terms are
    written the same and their assertions differ, the writing does not
    determine the assertions.

Chosen here (reading C-W1 of the paper)
    A writing is a function from a result's terms to letters, not a field of
    the result.  Letters are renamed so a writing is a restricted growth
    string.  The writing determines the assertions exactly when, in each
    relation, the multiplicity is constant on every rectangle of pairs of
    terms that share a pair of letters.  A writing `w'` is coarser than `w`
    when it writes together every pair `w` writes together, and possibly
    more.

Cited from the ninth derivation (`ninth.state`) and re-checked
    `DState`, `same` and `swap` mention no writing: they survive and are
    imported.  A writing is not a third multiplicity beside `r` and `s`
    (the state is the ninth's).
"""

from __future__ import annotations

from collections import defaultdict
from itertools import permutations

from ninth.state import RELATIONS, DState, rewrite

__all__ = [
    "automorphisms",
    "bell",
    "coarser_than",
    "determines",
    "determines_rel",
    "injective",
    "orbit_count_burnside",
    "permute_writing",
    "read_from",
    "restricted_growth",
    "terms_after_writing",
    "writing_orbits",
    "writings",
]


def writings(n: int) -> tuple[tuple[int, ...], ...]:
    """Restricted growth strings of length `n`: writings up to renaming letters."""
    if n < 0:
        raise ValueError("the number of terms is not negative")
    if n == 0:
        return ((),)
    found: list[tuple[int, ...]] = []

    def rec(prefix: list[int], nxt: int) -> None:
        if len(prefix) == n:
            found.append(tuple(prefix))
            return
        for letter in range(nxt):
            prefix.append(letter)
            rec(prefix, nxt)
            prefix.pop()
        prefix.append(nxt)
        rec(prefix, nxt + 1)
        prefix.pop()

    rec([], 0)
    return tuple(found)


def bell(n: int) -> int:
    """How many writings of `n` terms there are, up to renaming letters."""
    return len(writings(n))


def restricted_growth(writing: tuple[int, ...]) -> tuple[int, ...]:
    """The writing with letters renamed by first occurrence (its class up to renaming letters)."""
    seen: dict[int, int] = {}
    out: list[int] = []
    for letter in writing:
        if letter not in seen:
            seen[letter] = len(seen)
        out.append(seen[letter])
    return tuple(out)


def permute_writing(writing: tuple[int, ...], p: tuple[int, ...]) -> tuple[int, ...]:
    """The writing after the terms are rewritten by `p` (term `t` becomes term `p[t]`).

    In the same convention as `rewrite`: the letter of term `t` moves to term
    `p[t]`, so the result is read back up to renaming letters.
    """
    n = len(writing)
    moved = [0] * n
    for t in range(n):
        moved[p[t]] = writing[t]
    return restricted_growth(tuple(moved))


def automorphisms(state: DState) -> tuple[tuple[int, ...], ...]:
    """The term permutations that leave `state` unchanged (its automorphisms)."""
    return tuple(p for p in permutations(range(state.n)) if rewrite(state, p) == state)


def writing_orbits(state: DState) -> tuple[tuple[int, ...], ...]:
    """One writing of `state` per orbit under its automorphisms — its distinct labeled writings.

    Two writings that a term-automorphism of `state` carries onto each other
    (up to renaming letters) label the same result, since results that differ
    only in how their terms are written are the same.
    """
    autos = automorphisms(state)
    seen: set[tuple[int, ...]] = set()
    reps: list[tuple[int, ...]] = []
    for w in writings(state.n):
        rep = min(permute_writing(w, p) for p in autos)
        if rep not in seen:
            seen.add(rep)
            reps.append(rep)
    return tuple(reps)


def orbit_count_burnside(state: DState) -> int:
    """The number of distinct writings by Burnside's count, independent of `writing_orbits`.

    The number of orbits of the writings under the automorphisms equals the
    average, over the automorphisms, of the writings each one fixes.
    """
    autos = automorphisms(state)
    fixed_total = 0
    for p in autos:
        fixed_total += sum(1 for w in writings(state.n) if permute_writing(w, p) == w)
    return fixed_total // len(autos)


def injective(writing: tuple[int, ...]) -> bool:
    """Does every term have a letter no other term has?"""
    return len(set(writing)) == len(writing)


def _rectangles(state: DState, writing: tuple[int, ...], rel: str) -> dict[tuple[int, int], set[int]]:
    """Multiplicities on each letter-pair rectangle of one relation."""
    n = state.n
    rect: dict[tuple[int, int], set[int]] = defaultdict(set)
    for x in range(n):
        for y in range(n):
            rect[(writing[x], writing[y])].add(state.mult_of(rel, x, y))
    return rect


def determines_rel(state: DState, writing: tuple[int, ...], rel: str) -> bool:
    """Does `writing` determine the assertions of one relation?"""
    if len(writing) != state.n:
        raise ValueError("a writing assigns a letter to every term")
    if rel not in RELATIONS:
        raise ValueError("an assertion is written with r or with s")
    return all(len(values) == 1 for values in _rectangles(state, writing, rel).values())


def determines(state: DState, writing: tuple[int, ...]) -> bool:
    """Does `writing` determine the assertions of both relations?"""
    return determines_rel(state, writing, "r") and determines_rel(state, writing, "s")


def coarser_than(writing: tuple[int, ...], coarser: tuple[int, ...]) -> bool:
    """Does `coarser` write together every pair `writing` writes together?"""
    if len(writing) != len(coarser):
        raise ValueError("two writings of one state have the same length")
    n = len(writing)
    return all(
        coarser[i] == coarser[j]
        for i in range(n)
        for j in range(n)
        if writing[i] == writing[j]
    )


def read_from(state: DState, writing: tuple[int, ...]) -> dict[str, dict[tuple[int, int], int]] | None:
    """The letter-pair multiplicities, or `None` when the writing does not determine."""
    if not determines(state, writing):
        return None
    n = state.n
    out: dict[str, dict[tuple[int, int], int]] = {"r": {}, "s": {}}
    for rel in RELATIONS:
        for x in range(n):
            for y in range(n):
                out[rel][(writing[x], writing[y])] = state.mult_of(rel, x, y)
    return out


def terms_after_writing(state: DState, writing: tuple[int, ...]) -> int:
    """How many terms remain after the writing.  A writing is not identifying."""
    if len(writing) != state.n:
        raise ValueError("a writing assigns a letter to every term")
    return state.n
