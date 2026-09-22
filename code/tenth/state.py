"""Two-relation states without names, and the unchosen tagged reading (tenth seed).

Given by the tenth seed
    The state is the ninth's: terms, a multiplicity per ordered pair in `r`
    and in `s`, nothing given.  A leftover is not an assertion.

Chosen here (C-L1)
    A result is a two-relation state up to sameness, as under the ninth.
    Leftover is not a field of the state.

Unchosen, kept (C-L2)
    A result is a ninth state together with the leftover of the incoming
    change; the beginning is tagged "nothing left".  `Tagged` is that pair.
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

from tenth.leftover import LeftOver

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
    "remove",
    "rewrite",
    "same",
    "swap",
    "tagged_start",
    "written",
]


@dataclass(frozen=True)
class Tagged:
    """A ninth state with leftover status (unchosen reading C-L2)."""

    state: DState
    leftover: LeftOver

    @property
    def n(self) -> int:
        """How many terms."""
        return self.state.n

    @property
    def size(self) -> int:
        """The ninth's size of the underlying state (leftover is not an assertion)."""
        return self.state.size


def tagged_start() -> Tagged:
    """The empty beginning, tagged nothing left (no incoming change)."""
    return Tagged(empty(), LeftOver.NOTHING_LEFT)
