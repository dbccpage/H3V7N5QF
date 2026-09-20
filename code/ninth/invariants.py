"""What a change of the ninth seed keeps, and what it does not keep.

Derived (paper, `lean4/Ninth/Step.lean`, `Cost.lean`)
    Along one change the size (terms plus both totals) moves by exactly one
    (`size_moves_by_one`), so the cost rises by at most one; a state with a
    term leaves a state with a term (`term_stays`: the one irreversible
    change is leaving the empty state); well-formedness is kept.

Refuted (witnesses in `ninth.evidence`)
    Every count the earlier derivations kept — terms, each relation's total,
    every multiplicity, the size, the fewest classes of a split in either
    relation, "no `xrx`", "no `xsx`" — can fall along a change, as under the
    fifth to eighth seeds (`lowered`).  The eighth's "the names once one term
    stay one term" has no object.

Cited from the eighth derivation (`eighth.invariants`) and re-checked
    `lowered` (which of the kept counts and properties an outcome has below
    its state, per relation) and `fewest_classes` (a function of a part
    asserting no loop; 0 on the empty state) mention no name and no given
    and survive; they are imported.
"""

from __future__ import annotations

from eighth.invariants import fewest_classes, lowered

from ninth.state import DState, has_term

__all__ = ["fewest_classes", "lowered", "size_moves_by_one", "term_stays"]


def size_moves_by_one(state: DState, out: DState) -> bool:
    """Is the size of `out` exactly one above or one below the size of `state`?"""
    return abs(out.size - state.size) == 1


def term_stays(state: DState, out: DState) -> bool:
    """If `state` has a term, does `out` have one?"""
    return not has_term(state) or has_term(out)
