"""The fewest changes to a result, and what is recorded for it.

Cited from the twenty-third derivation (`twentythird.cost`) and re-checked
    The fewest assertions among the states of the result of a twenty-third
    state (`fewest`, by raising sets of terms), its cost `n + fewest`
    (`cost23`), the states asserting the fewest (`fewest_states`) and its
    record (terms, assertions in `r`, in `s` of a state asserting the fewest,
    `record23`) are about the assertions only.  A state here asserts what its
    `base` asserts, so they are read on the base (no change).

Derived (paper, D5; `lean4_core/Twentyfourth/Cost.lean`, `cost24`)
    The fewest changes to a result is the twenty-third's cost of its base plus
    the number of its filled terms: the twenty-second's `phi` plus the filled
    count rises by at most one per change (a filling by exactly one; an
    identification lowers `phi` and keeps or lowers the filled count), and
    additions then fillings reach it.  Under the unchosen C-F2 each filling
    counts (`cost_counted`).
"""

from __future__ import annotations

from twentythird.cost import cost as cost23
from twentythird.cost import fewest, fewest_states
from twentythird.cost import record as record23
from twentythird.state import plain_cost

from twentyfourth.state import FState

__all__ = ["cost", "cost23", "cost_counted", "fewest", "fewest_states", "potential", "record23"]


def cost(state: FState) -> int:
    """The fewest changes from the empty state to the result of `state` (reading C-F1)."""
    return cost23(state.base) + state.filled_count


def cost_counted(state: FState) -> int:
    """The fewest changes under C-F2: every filling counted."""
    return cost23(state.base) + state.fillings


def potential(state: FState) -> int:
    """The twenty-second's `phi` of the base (terms plus the plain state's assertions) plus the filled terms."""
    return plain_cost(state.base) + state.filled_count
