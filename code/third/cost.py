"""The fewest changes that reach a result, in closed form, under the third seed.

Derived (paper, `lean4/Third/Cost.lean`)
    Let what is given have `n0 = 2` terms and `m0` assertions (`1` without
    `bra`, `2` with).  A state with names is a result exactly when `a` and
    `b` are two terms and every given assertion is asserted between them;
    the fewest changes to it is `(n + m) - (n0 + m0)`, its size minus that of
    what is given — and under this seed *every* sequence of changes reaching
    it has exactly that length, since each change raises the size by one.
    Without names a state is a result exactly when some assertion is asserted
    (without `bra`) or some pair is asserted both ways (with `bra`).

Cited from the second derivation (`second.cost`) and re-checked
    The functions below are the second derivation's: each is a function of
    one state and the alternative for `bra`, and mentions no change.  The
    closed form they compute is proved again from the third seed
    (`fewest_changes2_A`, `fewest_changes2_B`, `Reach2.length_unique`), and
    `third.evidence` compares it with the round of every explored result.
"""

from __future__ import annotations

from second.cost import (
    contains_given,
    cost,
    cost_anchored,
    cost_free,
    cost_free_by_placement,
    given_size,
    has_two_way,
)

__all__ = [
    "contains_given",
    "cost",
    "cost_anchored",
    "cost_free",
    "cost_free_by_placement",
    "given_size",
    "has_two_way",
]
