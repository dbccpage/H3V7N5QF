"""The fewest changes that reach a result, in closed form, under the seventh seed.

Derived (paper, `lean4/Seventh/Cost.lean`)
    Let `size = terms + Σ multiplicities`.  Every change moves the size by
    exactly one: up for the two additions, down for a removal or an
    identification (the sixth's `Step6.size_step`, re-checked through the
    naming map on states with a term; on the empty state the only change
    adds a term).  The empty state has size 0, so a result of size `k` needs
    at least `k` changes; and `k` additions — the terms, then the assertions
    — reach it.  So the fewest changes from what is given to any well-formed
    state is

        its size,

    with nothing destroyed, since nothing is given to destroy.  Every
    shortest sequence is additions only (`raises_by_one`: a change raises
    the cost by exactly one exactly when it is an addition).  The cost is the
    same in every writing (rewriting keeps the size).

Cited from the fourth and sixth derivations (`fourth.cost`, `sixth.cost`) and
re-checked
    The sixth's `cost_free` (`size − size(given) + 2·lost_free`, measured
    from `arb`) is imported as `cost_sixth` for the comparison only: it is
    the sixth's own formula, cited, and it does *not* survive as the cost of
    this seed (the one-term state asserting nothing costs 2 there, 1 here).
    What survives of the fourth's and sixth's "size difference on states
    containing what is given" is the case `size(given) = 0`: the size itself.
    `given_size` (the first's, `2 + m0`) has no object; `size(given)` is 0.
"""

from __future__ import annotations

from sixth.cost import cost_free as cost_sixth_free

from seventh.changes import Change, is_addition
from seventh.state import MState

__all__ = ["GIVEN_SIZE", "cost", "cost_sixth", "cost_sixth_free", "raises_by_one"]

#: The size of what is given: no terms, nothing asserted.
GIVEN_SIZE = 0


def cost(state: MState) -> int:
    """Fewest changes from what is given (the empty state) to `state`: its size."""
    if state.names is not None:
        raise ValueError("a state of the seventh seed carries no names")
    return state.size - GIVEN_SIZE


def cost_sixth(state: MState, bra: bool) -> int:
    """The sixth seed's fewest changes to a state with a term (any rewriting), cited for the comparison.

    `size − size(given) + 2·lost_free`, the sixth's own formula; it has no
    value on the empty state, which the sixth seed never reaches.
    """
    found = cost_sixth_free(state, bra)
    if found is None:
        raise ValueError("the sixth seed has no result without terms")
    return found


def raises_by_one(state: MState, change: Change) -> bool:
    """Does `change` raise the cost by exactly one?  Exactly when it is an addition.

    A removal or an identification lowers the size by one; `state` is only
    there to keep the shape of the earlier derivations' rule.
    """
    del state
    return is_addition(change)
