"""Two-relation states without names, and the unchosen recorded reading (twelfth seed).

Given by the twelfth seed
    The state is the ninth's: terms, a multiplicity per ordered pair in `r`
    and in `s`, nothing given.  Identifying two terms records, for each
    relation, which assertions of those two terms become one assertion.
    The record is kept with the result.

Chosen here (C-M1)
    A result is a two-relation state up to sameness, as under the ninth.
    The record is not a field of the state; it is extra data on the
    identification that produced a result.

Unchosen, kept (C-M2)
    A result is a ninth state together with the identification record of
    the most recent identification, or no record if none has occurred.
    The record persists through later non-identify changes.  `Recorded`
    is that pair.
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

from twelfth.record import IdentRecord

__all__ = [
    "RELATIONS",
    "DState",
    "MState",
    "Pair",
    "Recorded",
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
    "recorded_start",
    "remove",
    "rewrite",
    "same",
    "swap",
    "written",
]


@dataclass(frozen=True)
class Recorded:
    """A ninth state with an identification record (unchosen reading C-M2).

    `record` is `None` when no identification has occurred yet.
    """

    state: DState
    record: IdentRecord | None

    @property
    def n(self) -> int:
        """How many terms."""
        return self.state.n

    @property
    def size(self) -> int:
        """The ninth's size of the underlying state (a record is not an assertion)."""
        return self.state.size


def recorded_start() -> Recorded:
    """The empty beginning, with no identification record."""
    return Recorded(empty(), None)
