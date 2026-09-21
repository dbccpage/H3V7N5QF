"""Two-relation states without names, and the unchosen coarser reading (thirteenth seed).

Given by the thirteenth seed
    The state is the ninth's: terms, a multiplicity per ordered pair in `r`
    and in `s`, nothing given.  A coarser writing of an assertion forgets
    whether it was written with `r` or with `s`.  For every result, record
    also its coarser writing.

Chosen here (C-C1)
    A result is a two-relation state up to sameness, as under the ninth.
    The coarser writing is not a field of the state; it is extra data
    computed from the two multiplicities.

Unchosen, kept (C-C2)
    A result is the coarser writing: a one-relation state whose multiplicity
    at each pair is the sum of the two.  Two finer states with the same sum
    are one result.  `Coarse` is that one-relation state.
"""

from __future__ import annotations

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
    "Coarse",
    "DState",
    "MState",
    "Pair",
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
    "written",
]

Coarse = MState
