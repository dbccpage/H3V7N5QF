"""What no change of the fourth seed lowers.

Derived (paper, `lean4/Fourth/Contain.lean`, `Cost.lean`)
    A change adds one term or raises one multiplicity by one and takes
    nothing away.  So along a change the number of terms and every
    multiplicity never decrease (hence neither the total multiplicity nor
    the number of asserted assertions), and the size (terms plus total
    multiplicity) rises by exactly one (`never_decreases`).  The fewest
    classes of a split of the terms with no two related terms in one class
    never decreases either.

Cited from the second and third derivations (`second.invariants`) and re-checked
    `fewest_classes` is a function of which pairs are related, which the
    multiplicity does not change; it survives the counting as a function of
    the support.  Its monotonicity was derived there from the carrying map;
    under this seed the support of a state is contained in the support of the
    outcome, and the statement restricts (Lean: `Reach4.split_mono`).

Computed
    `fourth.evidence` checks both on every unobstructed change within the bound.
"""

from __future__ import annotations

from second.invariants import fewest_classes as fewest_classes_of_support

from fourth.state import MState, support

__all__ = ["fewest_classes", "never_decreases"]


def fewest_classes(state: MState) -> int:
    """The fewest classes of a split with no two related terms in one class."""
    return fewest_classes_of_support(support(state))


def never_decreases(state: MState, out: MState) -> bool:
    """Terms and every multiplicity did not decrease from `state` to `out`, and the size rose by one."""
    return (
        out.n >= state.n
        and all(k <= out.mult_of(x, y) for x, y, k in state.counted)
        and out.size == state.size + 1
    )
