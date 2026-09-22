"""The fewest changes that reach a result, under the twelfth seed.

Cited from the ninth derivation (`ninth.cost`) and re-checked
    Under C-M1 the fewest changes is the size: a record is not an assertion
    and is not counted.  `cost`, `part_costs`, `raises_by_one` and
    `GIVEN_SIZE` survive and are imported.

Derived (paper, `lean4/Twelfth/Compare.lean`)
    Under C-M2 the fewest changes to a recorded result is the BFS round, not
    always the ninth's size (an identification that attaches a record costs
    extra).  The count of recorded results is larger.
"""

from __future__ import annotations

from ninth.cost import GIVEN_SIZE, cost, cost_eighth, cost_part, part_costs, raises_by_one

from twelfth.explore import RecordedExploration
from twelfth.state import Recorded

__all__ = [
    "GIVEN_SIZE",
    "cost",
    "cost_eighth",
    "cost_part",
    "part_costs",
    "raises_by_one",
    "recorded_cost",
]


def recorded_cost(expl: RecordedExploration, recorded: Recorded) -> int | None:
    """Fewest changes from the empty beginning to `recorded` under C-M2, or `None` if unreached."""
    return expl.depth.get(recorded)
