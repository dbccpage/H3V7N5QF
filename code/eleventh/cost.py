"""The fewest changes that reach a result, under the eleventh seed.

Cited from the ninth derivation (`ninth.cost`) and re-checked
    Under C-W1 the fewest changes is the size: a writing is not an assertion
    and is not counted.  `cost`, `part_costs`, `raises_by_one` and
    `GIVEN_SIZE` survive and are imported.

Derived (paper, `lean4/Eleventh/Compare.lean`)
    Under C-W2 the fewest changes to a labeled result is still the ninth's
    size of the underlying state (a writing is not a change); the count of
    labeled results is larger.
"""

from __future__ import annotations

from ninth.cost import GIVEN_SIZE, cost, cost_eighth, cost_part, part_costs, raises_by_one

from eleventh.explore import LabeledExploration
from eleventh.state import Labeled

__all__ = [
    "GIVEN_SIZE",
    "cost",
    "cost_eighth",
    "cost_part",
    "labeled_cost",
    "part_costs",
    "raises_by_one",
]


def labeled_cost(expl: LabeledExploration, labeled: Labeled) -> int | None:
    """Fewest changes from the empty beginning to `labeled` under C-W2, or `None` if unreached."""
    return expl.depth.get(labeled)
