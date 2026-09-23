"""Leftover writings under the sixteenth seed: the fourteenth's, and which of them may be admitted.

Given by the sixteenth seed
    After every change, record what that change leaves.  A leftover is
    written neither `xry` nor `xsy`.  A recorded leftover `xℓy` may be
    admitted, adding the assertion `xry` or the assertion `xsy`; an
    unadmitted leftover is not an assertion.

Cited from the fourteenth derivation (`fourteenth.leftover`) and re-checked
    The leftover *writing* of a change of the four kinds survives: an
    addition leaves nothing, a removal of `(x, y)` leaves the pair written
    `xℓy` naming no relation, an identification leaves the merge writing.
    `LeftWriting`, `leftover_of`, `leftover_pair`, `leftover_nothing` and
    `leftover_merge` are imported.  What does not survive is the sentence
    that made every leftover inert: a pair writing of a recorded pair may
    now be admitted (`admissible`), and admitting is a change of the kind
    "adding an assertion".  A merge writing is not written `xℓy` and is not
    admissible; nothing is not a leftover to admit.

Chosen here (C-R1)
    An admission leaves nothing: it adds an assertion, and the leftover it
    admits becomes that assertion.
"""

from __future__ import annotations

from fourteenth.leftover import (
    LeftWriting,
    leftover_merge,
    leftover_nothing,
    leftover_of,
    leftover_pair,
    other_relation,
)

from sixteenth.changes import Change16, admissions_of
from sixteenth.state import RState

__all__ = [
    "LeftWriting",
    "admissible",
    "admissions_of_writing",
    "leftover_merge",
    "leftover_nothing",
    "leftover_of",
    "leftover_of16",
    "leftover_pair",
    "other_relation",
    "unadmitted_is_assertion",
]


def leftover_of16(rs: RState, change: Change16) -> LeftWriting:
    """The leftover writing of `change` on `rs`: an admission leaves nothing; otherwise the fourteenth's."""
    if change.admits:
        return leftover_nothing()
    return leftover_of(rs.state, change.ninth())


def admissible(writing: LeftWriting, rs: RState) -> bool:
    """May this writing be admitted on `rs`?  Exactly when it is a pair writing of a recorded pair."""
    return writing.kind == "pair" and 0 <= writing.x < rs.n and 0 <= writing.y < rs.n and rs.has_leftover(writing.x, writing.y)


def admissions_of_writing(writing: LeftWriting, rs: RState) -> tuple[Change16, ...]:
    """The changes that admit this writing on `rs`: into `r` and into `s`, or none."""
    if not admissible(writing, rs):
        return ()
    return admissions_of(writing.x, writing.y)


def unadmitted_is_assertion(writing: LeftWriting) -> bool:
    """Is an unadmitted leftover an assertion?  The seed says it is not; the writing uses neither `r` nor `s`."""
    return writing.is_assertion()
