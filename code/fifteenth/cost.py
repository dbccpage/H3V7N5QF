"""The fewest changes that reach a result, under the fifteenth seed.

Cited from the ninth derivation (`ninth.cost`) and re-checked
    Under C-A1 the fewest changes is the size: admission is not an assertion
    and is not counted.  `cost`, `part_costs`, `raises_by_one` and
    `GIVEN_SIZE` survive and are imported.

Derived (paper, `lean4/Fifteenth/Compare.lean`)
    Under C-A2 the fewest steps to a tagged result is its tagged depth,
    which can exceed the ninth's size (witness: the one-term state asserting
    nothing, tagged admitted, costs 2 against size 1).
"""

from __future__ import annotations

from ninth.cost import GIVEN_SIZE, cost, cost_eighth, cost_part, part_costs, raises_by_one

from fifteenth.explore import TaggedExploration
from fifteenth.state import Tagged

__all__ = [
    "GIVEN_SIZE",
    "cost",
    "cost_eighth",
    "cost_part",
    "part_costs",
    "raises_by_one",
    "tagged_cost",
]


def tagged_cost(expl: TaggedExploration, tagged: Tagged) -> int | None:
    """Fewest steps from the empty beginning to `tagged` under C-A2, or `None` if unreached."""
    return expl.depth.get(tagged)
