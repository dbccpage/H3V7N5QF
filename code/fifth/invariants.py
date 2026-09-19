"""What a change of the fifth seed keeps, and what it no longer keeps.

Derived (paper, `lean4/Fifth/Cost.lean`, `Step.lean`)
    Along one change the cost (size plus twice the destroyed givens) rises
    by at most one (`cost_rises_by_at_most_one`); the names, once one term,
    stay one term (`names_stay_merged`); legality and at least one term are
    kept.

Refuted (witnesses in `fifth.evidence`)
    The fourth derivation's counts that never decreased — the number of
    terms, every multiplicity, the total, the size, the fewest classes of a
    split — can all decrease now.  `never_decreases` is the fourth's test,
    imported so that the changes on which it fails can be counted; the
    fewest-classes count is the second's through the fourth, kept only for
    the same purpose.

Cited from the fourth derivation (`fourth.invariants`) and re-checked
    `fewest_classes` is a function of a state and survives as such; its
    monotonicity (4:D13) does not survive.  `never_decreases` is a test on a
    pair of states; its truth on every change (4:D6) does not survive.
"""

from __future__ import annotations

from fourth.invariants import fewest_classes, never_decreases

from fifth.cost import cost
from fifth.state import MState, names_one_term

__all__ = ["cost_rises_by_at_most_one", "fewest_classes", "lowered", "names_stay_merged", "never_decreases"]


def cost_rises_by_at_most_one(state: MState, out: MState, bra: bool) -> bool:
    """Is the cost of `out` at most the cost of `state` plus one (both being results)?"""
    before, after = cost(state, bra), cost(out, bra)
    return before is not None and after is not None and after <= before + 1


def names_stay_merged(state: MState, out: MState) -> bool:
    """If `a` and `b` are one term in `state`, are they one term in `out`?"""
    return not names_one_term(state) or names_one_term(out)


def lowered(state: MState, out: MState) -> tuple[str, ...]:
    """Which of the fourth's never-decreasing counts `out` has below `state`."""
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
    return tuple(found)
