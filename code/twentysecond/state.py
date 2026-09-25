"""States, the excess, the plain state and the result (twenty-second seed).

Given by the twenty-second seed
    The ninth seed's sentences, word for word, except one: "Two results that
    differ only in how their terms are written, or only by an `xry` and an
    `xsy` asserted together, are the same result."

Cited from the ninth derivation (`ninth.state`) and re-checked (no change)
    The state is the ninth's two-relation state without names (`DState`
    with `names = None`), the beginning its empty state, `canonical` its
    least writing under rewriting (acting on both relations at once), `swap`
    its exchange of the two relations, `rewrite` its rewriting.  None of them
    mentions sameness of results, so they stand as they are.

Chosen here (reading C-J1 of the paper)
    "Differ only by an `xry` and an `xsy` asserted together": one state is
    the other with one more `xry` and one more `xsy` on the same two terms
    (`x = y` allowed); "are the same result" makes the sameness the
    equivalence these steps and rewriting generate.

Derived (paper; `lean4_core/Twentysecond/Same.lean`, `Rename.lean`)
    Two states are the same result exactly when they have equally many terms
    and, under one rewriting, the same *excess* `M_r(x, y) − M_s(x, y)` at
    every ordered pair.  Each result has one *plain state* up to writing: at
    every pair at most one relation asserts (`plain`).  So the least writing
    of the plain state (`result_of`) is a complete invariant of a result.

Chosen here (reading C-R)
    What is recorded for a result (the terms and assertions it adds to what
    is given, nothing being given) is read on its plain state: its terms, its
    assertions in `r` and in `s` (`recorded`).  Their sum is the cost.
"""

from __future__ import annotations

from ninth.state import DState, MState, canonical, empty, forget_canonical_forms, of_r, rewrite, swap

__all__ = [
    "DState",
    "MState",
    "canonical",
    "common",
    "cost",
    "empty",
    "excess",
    "forget_canonical_forms",
    "is_plain",
    "of_r",
    "plain",
    "recorded",
    "result_of",
    "rewrite",
    "same",
    "swap",
    "together_count",
    "written",
]


def excess(state: DState, x: int, y: int) -> int:
    """`M_r(x, y) − M_s(x, y)`: how many more times `xry` is asserted than `xsy`."""
    i = x * state.n + y
    return state.r[i] - state.s[i]


def common(state: DState) -> tuple[int, ...]:
    """At every ordered pair, how many times it is asserted in both relations: `min(M_r, M_s)`."""
    return tuple(min(a, b) for a, b in zip(state.r, state.s))


def together_count(state: DState) -> int:
    """How many pairs asserted together the state holds (each an `xry` with its `xsy`)."""
    return sum(common(state))


def plain(state: DState) -> DState:
    """The plain state: every pair asserted together taken out, so no pair is asserted in both relations."""
    r = tuple(max(a - b, 0) for a, b in zip(state.r, state.s))
    s = tuple(max(b - a, 0) for a, b in zip(state.r, state.s))
    return DState(state.n, r, s)


def is_plain(state: DState) -> bool:
    """Is no pair asserted in both relations?"""
    return together_count(state) == 0


def result_of(state: DState) -> DState:
    """The result of `state`: the least writing of its plain state (equal exactly for same results)."""
    return canonical(plain(state))


def same(s: DState, t: DState) -> bool:
    """Are `s` and `t` the same result (rewriting, and pairs asserted together)?"""
    return s.n == t.n and result_of(s) == result_of(t)


def recorded(state: DState) -> tuple[int, int, int]:
    """What is recorded for the result of `state`: its terms, its assertions in `r`, in `s` (plain state)."""
    p = plain(state)
    return p.n, p.total_r, p.total_s


def cost(state: DState) -> int:
    """`n + Σ |excess|`: the terms plus the assertions of the plain state."""
    n, in_r, in_s = recorded(state)
    return n + in_r + in_s


def written(state: DState) -> str:
    """The state written in the seed's notation; the empty state in words."""
    if state.n == 0:
        return "no terms; asserted nothing"
    return state.written()
