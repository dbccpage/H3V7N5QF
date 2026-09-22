"""Two-relation states without names, and the unchosen labeled reading (eleventh seed).

Given by the eleventh seed
    The state is the ninth's: terms, a multiplicity per ordered pair in `r`
    and in `s`, nothing given.  A writing of terms may collide two terms
    that remain two.

Chosen here (C-W1)
    A result is a two-relation state up to sameness, as under the ninth.
    A writing is not a field of the state.

Unchosen, kept (C-W2)
    A result is a ninth state together with a writing of its terms (up to
    renaming letters).  `Labeled` is that pair.
"""

from __future__ import annotations

from dataclasses import dataclass

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

__all__ = [
    "RELATIONS",
    "DState",
    "Labeled",
    "MState",
    "Pair",
    "added",
    "canonical",
    "empty",
    "forget_canonical_forms",
    "forget_names",
    "has_term",
    "identify",
    "labeled_start",
    "name_terms",
    "nothing_in",
    "of_r",
    "of_s",
    "pair",
    "remove",
    "rewrite",
    "same",
    "swap",
    "written",
]


@dataclass(frozen=True)
class Labeled:
    """A ninth state with a writing of its terms (unchosen reading C-W2)."""

    state: DState
    writing: tuple[int, ...]

    def __post_init__(self) -> None:
        if len(self.writing) != self.state.n:
            raise ValueError("a writing assigns a letter to every term")

    @property
    def n(self) -> int:
        """How many terms."""
        return self.state.n

    @property
    def size(self) -> int:
        """The ninth's size of the underlying state (a writing is not an assertion)."""
        return self.state.size


def labeled_start() -> Labeled:
    """The empty beginning, with its only writing."""
    return Labeled(empty(), ())
