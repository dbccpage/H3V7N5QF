"""The fewest changes that reach a result, and what no change lowers, under the sixteenth seed.

Derived (paper, `lean4/Sixteenth/Cost.lean`, `lean4/Sixteenth/Reach.lean`)
    Let the *potential* of a state be its size (terms plus both totals, the
    ninth's) plus twice its record.  A term or a direct assertion raises it
    by one; a removal raises it by one (the multiplicity falls by one, the
    record rises by one); an admission lowers it by one; an identification
    lowers it by one (one term fewer, both totals and the record kept).  The
    empty state has potential 0, so a result of potential `k` needs at least
    `k` changes; and `k` changes reach it — the ninth's additions to the
    state part, then an addition and a removal for every recorded leftover.
    So the fewest changes from what is given to any well-formed state is

        its potential  =  size + 2 · record,

    and every shortest sequence uses only the changes that raise the
    potential: **no shortest sequence from the empty beginning admits or
    identifies**.  An assertion that arrives by admission costs three changes
    (add, remove, admit) where a direct addition costs one.

    Let the *mass* of a state be both totals plus the record.  No change
    lowers it: a removal moves one unit from a multiplicity to the record, an
    admission moves it back, an identification adds up, additions raise.
    The same holds of the mass on the pairs `(x, x)`.

Cited from the ninth derivation (`ninth.cost`) and re-checked
    The ninth's cost of a state — its size — survives on the results with an
    empty record and only there (`cost_ninth`, compared with `cost16` in
    `sixteenth.evidence`); the ninth's `raises_by_one` (the additions raise
    the size) survives as a fact about the state part and is replaced, for
    the cost, by `raises_potential` (removals raise too; admissions lower).
"""

from __future__ import annotations

from ninth.cost import cost as cost_ninth_state

from sixteenth.changes import Change16, raises_potential
from sixteenth.state import RState

__all__ = ["GIVEN_POTENTIAL", "cost16", "cost_ninth", "diag_mass", "lowers_by_one", "mass", "potential", "raises_by_one"]

#: The potential of what is given: no terms, nothing asserted, nothing recorded.
GIVEN_POTENTIAL = 0


def potential(rs: RState) -> int:
    """The size plus twice the record."""
    return rs.potential


def cost16(rs: RState) -> int:
    """Fewest changes from what is given (the empty state) to `rs`: its potential."""
    return potential(rs) - GIVEN_POTENTIAL


def cost_ninth(rs: RState) -> int:
    """The ninth's fewest changes to the state part (its size), cited for the comparison."""
    return cost_ninth_state(rs.state)


def mass(rs: RState) -> int:
    """Both totals plus the record: never lowered by a change."""
    return rs.mass


def diag_mass(rs: RState) -> int:
    """The mass on the pairs `(x, x)`: never lowered by a change."""
    return rs.diagonal_mass


def raises_by_one(rs: RState, change: Change16) -> bool:
    """Does `change` raise the cost by exactly one?  Exactly when it is a direct addition or a removal."""
    del rs
    return raises_potential(change)


def lowers_by_one(rs: RState, change: Change16) -> bool:
    """Does `change` lower the cost by exactly one?  Exactly when it is an admission or an identification."""
    del rs
    return not raises_potential(change)
