"""What a change of the seventh seed keeps, and what it does not keep.

Derived (paper, `lean4/Seventh/Step.lean`, `Cost.lean`)
    Along one change the size moves by exactly one (`size_moves_by_one`), so
    the cost rises by at most one; a state with a term leaves a state with a
    term (`term_stays`: the one irreversible change is leaving the empty
    state); well-formedness is kept.

Refuted (witnesses in `seventh.evidence`)
    Every count the earlier derivations kept — terms, every multiplicity,
    the total, the size, the fewest classes of a split, "no `xrx`" — can fall
    along a change, as under the fifth and sixth seeds (`lowered`).  The
    sixth's "the names once one term stay one term" has no object.

Cited from the fourth derivation (`fourth.invariants`) and re-checked
    `fewest_classes` is a function of a state asserting no `xrx` (a term
    related to itself fits in no class) and is compared only between such
    states; it mentions no name and survives as a function (it is 0 on the
    empty state).
"""

from __future__ import annotations

from fourth.invariants import fewest_classes

from seventh.state import MState, has_term

__all__ = ["fewest_classes", "lowered", "size_moves_by_one", "term_stays"]


def size_moves_by_one(state: MState, out: MState) -> bool:
    """Is the size of `out` exactly one above or one below the size of `state`?"""
    return abs(out.size - state.size) == 1


def term_stays(state: MState, out: MState) -> bool:
    """If `state` has a term, does `out` have one?"""
    return not has_term(state) or has_term(out)


def lowered(state: MState, out: MState) -> tuple[str, ...]:
    """Which of the earlier derivations' kept counts and properties `out` has below `state`."""
    found = []
    if out.n < state.n:
        found.append("terms")
    if out.m < state.m:
        found.append("total_multiplicity")
    if out.n == state.n and any(out.mult_of(x, y) < k for x, y, k in state.counted):
        found.append("a_multiplicity")
    if out.size < state.size:
        found.append("size")
    if state.legal and out.legal and fewest_classes(out) < fewest_classes(state):
        found.append("fewest_classes")
    if state.legal and not out.legal:
        found.append("no_xrx")
    return tuple(found)
