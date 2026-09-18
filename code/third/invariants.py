"""What no change of the third seed lowers.

Derived (paper, `lean4/Third/Contain.lean`, `Cost.lean`)
    A change adds one term or one assertion and takes nothing away.  So along
    a change the number of terms and the number of assertions never decrease,
    and the size (terms plus assertions) rises by exactly one
    (`never_decreases`).  The fewest classes of a split of the terms with no
    two related terms in one class never decreases either.

Cited from the second derivation (`second.invariants`) and re-checked
    `fewest_classes` is a function of one state.  Its monotonicity was
    derived there from the carrying map; under this seed the map is the
    identity, and the statement restricts (Lean: `Reach2.split_mono`, through
    the embedding of the third seed's changes into the second's).

Computed
    `third.evidence` checks both on every unobstructed change within the bound.
"""

from __future__ import annotations

from second.invariants import fewest_classes
from xry.state import State

__all__ = ["fewest_classes", "never_decreases"]


def never_decreases(state: State, out: State) -> bool:
    """Terms and assertions did not decrease from `state` to `out`, and the size rose by one."""
    return out.n >= state.n and out.m >= state.m and out.n + out.m == state.n + state.m + 1
