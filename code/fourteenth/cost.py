"""The fewest changes that reach a result, under the fourteenth seed.

Cited from the ninth derivation (`ninth.cost`) and re-checked
    Under C-F1 the fewest changes is the size: leftover is not an assertion
    and is not counted.  `cost`, `part_costs`, `raises_by_one` and
    `GIVEN_SIZE` survive and are imported.

Derived (paper, `lean4/Fourteenth/Compare.lean`)
    Under C-F2 the fewest changes to a tagged result is its tagged depth,
    which can exceed the ninth's size (witness: the one-term state asserting
    nothing, tagged with leftover `0ℓ0`, costs 3 against size 1).
"""

from __future__ import annotations

from ninth.cost import GIVEN_SIZE, cost, cost_eighth, cost_part, part_costs, raises_by_one

from fourteenth.explore import TaggedExploration
from fourteenth.state import Tagged

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
    """Fewest changes from the empty beginning to `tagged` under C-F2, or `None` if unreached."""
    return expl.depth.get(tagged)
