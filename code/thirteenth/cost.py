"""The fewest changes that reach a result, under the thirteenth seed.

Cited from the ninth derivation (`ninth.cost`) and re-checked
    Under C-C1 the fewest changes is the size: a coarser writing is not an
    assertion and is not counted.  `cost`, `part_costs`, `raises_by_one` and
    `GIVEN_SIZE` survive and are imported.  The size of the coarser writing
    equals the size of the finer state, so the cost descends.

Derived (paper, `lean4/Thirteenth/Compare.lean`)
    Under C-C2 the fewest changes to a coarser result is still the size
    (every finer preimage has that same size).  The count of coarser
    results is smaller.
"""

from __future__ import annotations

from ninth.cost import GIVEN_SIZE, cost, cost_eighth, cost_part, part_costs, raises_by_one

from thirteenth.explore import CoarseExploration
from thirteenth.state import Coarse

__all__ = [
    "GIVEN_SIZE",
    "coarse_cost",
    "cost",
    "cost_eighth",
    "cost_part",
    "part_costs",
    "raises_by_one",
]


def coarse_cost(expl: CoarseExploration, written: Coarse) -> int | None:
    """Fewest changes from the empty beginning to `written` under C-C2, or `None` if unreached."""
    return expl.depth.get(written)
