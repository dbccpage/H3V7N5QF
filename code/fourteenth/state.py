"""Two-relation states without names, and the unchosen tagged reading (fourteenth seed).

Given by the fourteenth seed
    The state is the ninth's: terms, a multiplicity per ordered pair in `r`
    and in `s`, nothing given.  A leftover is not an assertion.

Chosen here (C-F1)
    A result is a two-relation state up to sameness, as under the ninth.
    Leftover is not a field of the state.

Unchosen, kept (C-F2)
    A result is a ninth state together with the leftover writing of the
    incoming change; the beginning is tagged nothing.  `Tagged` is that pair.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations

from ninth.state import (
    RELATIONS,
    DState,
    MState,
    Pair,
    added,
    canonical,
    empty,
    forget_canonical_forms,
    forget_names,
    has_term,
    identify,
    name_terms,
    nothing_in,
    of_r,
    of_s,
    pair,
    remove,
    rewrite,
    same,
    swap,
    written,
)

from fourteenth.leftover import (
    LeftWriting,
    leftover_merge_survivor,
    leftover_nothing,
    leftover_pair,
)

__all__ = [
    "RELATIONS",
    "DState",
    "MState",
    "Pair",
    "Tagged",
    "added",
    "canonical",
    "empty",
    "forget_canonical_forms",
    "forget_names",
    "has_term",
    "identify",
    "name_terms",
    "nothing_in",
    "of_r",
    "of_s",
    "pair",
    "canonical_tagged",
    "remove",
    "rewrite",
    "same",
    "swap",
    "tagged_start",
    "written",
]


@dataclass(frozen=True)
class Tagged:
    """A ninth state with leftover writing (unchosen reading C-F2)."""

    state: DState
    leftover: LeftWriting

    @property
    def n(self) -> int:
        """How many terms."""
        return self.state.n

    @property
    def size(self) -> int:
        """The ninth's size of the underlying state (leftover is not an assertion)."""
        return self.state.size


def tagged_start() -> Tagged:
    """The empty beginning, tagged nothing (no incoming change)."""
    return Tagged(empty(), leftover_nothing())


def canonical_tagged(state: DState, leftover: LeftWriting) -> Tagged:
    """The canonical tagged result of a state and the leftover of the change that reached it.

    Under C-F2 a result is a state with the leftover of the incoming change,
    counted up to writing.  The state and the leftover's terms must be
    renumbered *together*, so that the tag names the result's own terms: two
    results the same up to a term-renaming that also carries the leftover are
    one result.  The leftover's terms are given in the state's numbering — a
    removal's pair `(x, y)`, or an identification's surviving term `min(x, y)`
    (the other term is gone from the result).  This minimizes `(r, s, terms)`
    over the renumberings, so the state is `canonical(state)` and the tag is
    read in that same numbering.
    """
    n = state.n
    if leftover.kind == "nothing":
        return Tagged(canonical(state), leftover_nothing())
    if leftover.kind == "pair":
        terms: tuple[int, ...] = (leftover.x, leftover.y)
    else:  # a merge: only the surviving term is in the result and is writing-invariant
        terms = (min(leftover.x, leftover.y),)
    best_key: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]] | None = None
    best_state: DState | None = None
    best_terms: tuple[int, ...] = ()
    for perm in permutations(range(n)):
        moved_state = rewrite(state, perm)
        moved_terms = tuple(perm[t] for t in terms)
        key = (moved_state.r, moved_state.s, moved_terms)
        if best_key is None or key < best_key:
            best_key = key
            best_state = moved_state
            best_terms = moved_terms
    assert best_state is not None  # range(n) has at least the identity permutation
    if leftover.kind == "pair":
        tag = leftover_pair(best_terms[0], best_terms[1])
    else:
        tag = leftover_merge_survivor(best_terms[0])
    return Tagged(best_state, tag)
