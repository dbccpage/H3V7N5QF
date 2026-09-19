"""The fewest changes that reach a result, in closed form, under the eighth seed.

Derived (paper, `lean4/Eighth/Cost.lean`)
    Let `size = terms + Σ r-multiplicities + Σ s-multiplicities` and let
    `lost` be the sixth's destroyed givens read on the `r` part (the given
    lives in `r` alone).  Then `size + 2·lost` rises by at most one per
    change — an `s` addition or removal moves the `s` total by one and the
    `r` part not at all; an identification keeps both totals and lowers the
    terms by one, and destroys at most one given (the sixth's lemma on the `r`
    part); the `r` changes are the sixth's — and the fewest changes from what
    is given to any well-formed state is

        size − size(given) + 2·lost  =  the sixth's cost of the `r` part + the `s` total.

    So the cost is additive per relation: the `r` part costs what it cost
    under the sixth seed, the `s` part costs exactly its total (as under the
    seventh seed, where nothing is given).  Under FREE the names are placed
    to make the `r` part's destroyed givens least; the `s` part has no say.

Cited from the sixth derivation (`sixth.cost`) and re-checked
    `cost`, `cost_free`, `lost`, `lost_free`, `merged_optimal` and
    `raises_by_one` are the sixth's on one multiplicity function; applied to
    the `r` part they give the `r` half of this seed's cost and rule, and
    survive there.  `given_size` (the first's) is the size of what is given
    (nothing in `s`): no change.
"""

from __future__ import annotations

from sixth.cost import cost as cost_part
from sixth.cost import cost_free_by_placement as cost_free_by_placement_part
from sixth.cost import given_size, lost, lost_free, merged_optimal
from fifth.changes import Change as ChangeFifth
from sixth.cost import raises_by_one as raises_by_one_part
from xry.changes import Kind

from eighth.changes import Change
from eighth.state import DState

__all__ = ["cost", "cost_free_by_placement", "destroyed", "given_size", "lost", "lost_free", "merged_optimal", "raises_by_one"]


def destroyed(state: DState, bra: bool) -> int:
    """The destroyed givens of a result under the sameness its names imply (read on the `r` part)."""
    part = state.r_part()
    return lost_free(part, bra) if part.names is None else lost(part, bra)


def cost(state: DState, bra: bool) -> int | None:
    """Fewest changes from what is given to `state` under the sameness its names imply; `None` if not a result."""
    part = cost_part(state.r_part(), bra)
    return None if part is None else part + state.total_s


def cost_free_by_placement(state: DState, bra: bool) -> int | None:
    """`cost` under FREE computed the long way: the best placement of the names on the `r` part."""
    part = cost_free_by_placement_part(state.r_part(), bra)
    return None if part is None else part + state.total_s


def raises_by_one(state: DState, change: Change, bra: bool) -> bool:
    """Does `change` (names kept) raise the cost by exactly one?

    An `s` addition always; an `s` removal never; a term always; an `r`
    change or an identification exactly when the sixth's rule says so on the
    `r` part.
    """
    if change.kind is Kind.ADD_ASSERTION and change.rel == "s":
        return True
    if change.kind is Kind.REMOVE and change.rel == "s":
        return False
    return raises_by_one_part(state.r_part(), ChangeFifth(change.kind, change.x, change.y), bra)
