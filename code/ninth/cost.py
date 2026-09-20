"""The fewest changes that reach a result, in closed form, under the ninth seed.

Derived (paper, `lean4/Ninth/Cost.lean`)
    Let `size = terms + Σ r-multiplicities + Σ s-multiplicities`.  Every
    change moves the size by exactly one: up for the additions, down for a
    removal or an identification (the eighth's `Step8.size_step`, re-checked
    through the naming map on states with a term; on the empty state the
    only change adds a term).  The empty state has size 0, so a result of
    size `k` needs at least `k` changes; and `k` additions — the terms, then
    the `r` assertions, then the `s` assertions — reach it.  So the fewest
    changes from what is given to any well-formed state is

        its size,

    the seventh's collapse, with both totals counted.  **The eighth's
    additivity survives in the seventh's shape and no other:**

        size  =  cost₇(r part) + Σ s  =  cost₇(s part) + Σ r,

    where `cost₇` is the seventh's cost of a one-relation state (its size);
    but the sum of the two parts' costs is `size + terms`, since each part
    counts the terms the two relations share.  The cost is a sum of the two
    relations' totals and *one* count of terms, not a sum of two
    per-relation costs (`part_costs`).  Every shortest sequence is additions
    only (`raises_by_one`: a change raises the cost by exactly one exactly
    when it is an addition, of either relation).  The cost is the same in
    every writing.

Cited from the seventh and eighth derivations (`seventh.cost`, `eighth.cost`)
and re-checked
    The seventh's `cost` (the size of a one-relation state) is imported as
    `cost_part` and applied to a part; it survives as the cost of each part.
    The eighth's `cost` under any rewriting (the sixth's cost of the `r` part
    measured from `arb` plus the `s` total) is imported as `cost_eighth` for
    the comparison only: it does *not* survive as the cost of this seed
    (the one-term state costs 2 there, 1 here; `ara` once costs 1 there, 2
    here; `asa` once costs 3 there, 2 here).  What survives of the eighth's
    and fourth's "size difference on states containing what is given" is
    the case `size(given) = 0`: the size itself.
"""

from __future__ import annotations

from eighth.cost import cost as cost_eighth_any
from seventh.cost import cost as cost_part

from ninth.changes import Change, is_addition
from ninth.state import DState

__all__ = ["GIVEN_SIZE", "cost", "cost_eighth", "cost_part", "part_costs", "raises_by_one"]

#: The size of what is given: no terms, nothing asserted.
GIVEN_SIZE = 0


def cost(state: DState) -> int:
    """Fewest changes from what is given (the empty state) to `state`: its size."""
    if state.names is not None:
        raise ValueError("a state of the ninth seed carries no names")
    return state.size - GIVEN_SIZE


def part_costs(state: DState) -> tuple[int, int]:
    """The seventh's cost of the `r` part and of the `s` part (each its size: the terms counted in both)."""
    return cost_part(state.r_part()), cost_part(state.s_part())


def cost_eighth(state: DState, bra: bool) -> int:
    """The eighth seed's fewest changes to a state with a term (any rewriting), cited for the comparison.

    The sixth's cost of the `r` part measured from `arb` (with or without
    `bra`) plus the `s` total; it has no value on the empty state, which the
    eighth seed never reaches.
    """
    found = cost_eighth_any(state, bra)
    if found is None:
        raise ValueError("the eighth seed has no result without terms")
    return found


def raises_by_one(state: DState, change: Change) -> bool:
    """Does `change` raise the cost by exactly one?  Exactly when it is an addition, of either relation.

    A removal or an identification lowers the size by one; `state` is only
    there to keep the shape of the earlier derivations' rule.
    """
    del state
    return is_addition(change)
