"""The fewest changes to a result, and what is recorded for it.

Cited from the twenty-third derivation (`twentythird.cost`) and re-checked
    `cost` (terms plus the fewest assertions among the states of a
    twenty-third result, reached by raising sets of terms), `fewest`,
    `fewest_states`, `record` (the terms, and the assertions in `r` and in
    `s` of a state asserting the fewest) and `lower_bound` are about the
    assertions of a result alone, which the fillings do not touch: imported
    (no change) and applied to a state's multiplicities.

Derived (paper, D5; `lean4_core/Twentyfifth/Cost.lean`)
    The fewest changes to a result here is the twenty-third's cost of its
    assertions plus the number of its filled triples: a change raises `phi`
    plus the filled triples by at most one (a filling raises the triples by
    one and leaves `phi`; an identification never adds a triple), and
    additions to a state asserting the fewest, then the fillings, reach the
    result in that many changes.

Chosen here (reading C-R)
    What is recorded for a result: the twenty-third's record (a filled triple
    is neither a term nor an assertion), and which of its filled triples
    balance (`twentyfifth.state.balance_record`).
"""

from __future__ import annotations

from twentythird.cost import cost as cost23
from twentythird.cost import fewest, fewest_states, lower_bound
from twentythird.cost import record as record23

from twentyfifth.state import FState

__all__ = ["cost", "cost23", "fewest", "fewest_states", "lower_bound", "record", "record23"]


def cost(fs: FState) -> int:
    """The fewest changes from the empty state to the result of `fs`."""
    return cost23(fs.state) + len(fs.filled)


def record(fs: FState) -> tuple[int, int, int]:
    """What the result of `fs` adds to what is given: terms, assertions in `r`, in `s` (the twenty-third's)."""
    return record23(fs.state)
