"""Two-relation states without names, and the unchosen tagged reading (fifteenth seed).

Given by the fifteenth seed
    The state is the ninth's: terms, a multiplicity per ordered pair in `r`
    and in `s`, nothing given.  Admission is not an assertion.

Chosen here (C-A1)
    A result is a two-relation state up to sameness, as under the ninth.
    Admission is not a field of the state.

Unchosen, kept (C-A2)
    A result is a ninth state together with an admission record; the
    beginning is not admitted.  `Tagged` is that pair.
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

from fifteenth.admission import Admission, not_admitted_record

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
    """A ninth state with an admission record (unchosen reading C-A2)."""

    state: DState
    admission: Admission

    @property
    def n(self) -> int:
        """How many terms."""
        return self.state.n

    @property
    def size(self) -> int:
        """The ninth's size of the underlying state (admission is not an assertion)."""
        return self.state.size

    @property
    def admitted(self) -> bool:
        """Is this tagged result admitted?"""
        return self.admission.admitted


def tagged_start() -> Tagged:
    """The empty beginning, not admitted (reaching has not yet happened)."""
    return Tagged(empty(), not_admitted_record())
