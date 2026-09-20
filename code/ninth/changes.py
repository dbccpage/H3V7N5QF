"""Changes of the ninth seed: the eighth's four kinds over two relations, from a state that may be empty.

Given by the ninth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Nothing else is a change.  Adding an
    assertion raises its multiplicity by one; removing lowers it by one.
    Identifying two terms replaces both by one term in every assertion — of
    either relation.  Nothing is forbidden.

Cited from the eighth derivation (`eighth.changes`) and re-checked
    `Change` (the record of one change, with the relation of an assertion),
    `KINDS`, `is_change`, `changes` (identifications, removals in `r` then
    in `s`, a term, every ordered pair as an addition in `r` then in `s` —
    fewest additions first), `perform` and `makes_some_loop` mention no name
    and no given: they survive and are imported.  On the empty state `changes`
    lists "add a term" alone, which is the seed's own remark that the first
    change can only add a term.  The eighth's `attempt_counts` (the total,
    and per relation how many changes make some loop asserted) survives and
    is extended with the number of additions.

Cited from the seventh derivation (`seventh.changes`) and re-checked
    `is_addition`, `first_changes` and the count of additions are written
    again for two relations: `1 + 2n²` additions instead of `1 + n²`.

Derived (paper §4 D3, computed; a term stays: `lean4/Ninth/Step.lean`)
    * A result with `n` terms and `d_r + d_s` asserted pairs (diagonal pairs
      included) has `C(n, 2) + d_r + d_s + 1 + 2n²` changes, `1 + 2n²` of
      them additions; the empty state has one change, adding a term.  The
      count is the list in this module, not a Lean theorem (`Step9.proj` is
      not a count).
    * A change on a state with a term leaves a state with a term.

Chosen here (readings C5⁗ and C6 of the eighth paper, restated)
    * Removing what is not asserted, and identifying a term with itself,
      change nothing and are not changes; adding what is asserted is a change.
    * An identification adds up the multiplicities of the merged pairs in
      each relation separately.
    * Fewest additions first: identifications, removals in `r`, removals in
      `s` (no addition), then a term, then the additions in `r`, then in `s`.
"""

from __future__ import annotations

from eighth.changes import KINDS, Change, Kind, changes, is_change, makes_some_loop, perform
from eighth.changes import attempt_counts as attempt_counts_eighth

from ninth.state import DState, empty

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "first_changes",
    "is_addition",
    "is_change",
    "makes_some_loop",
    "perform",
]


def is_addition(change: Change) -> bool:
    """Does `change` add a term or an assertion (of either relation)?"""
    return change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)


def first_changes() -> tuple[Change, ...]:
    """The changes of the empty state: adding a term, and nothing else."""
    return changes(empty())


def attempt_counts(state: DState) -> tuple[int, int, int, int]:
    """How many changes `state` has; how many are additions; how many make some `xrx`, some `xsx` asserted.

    `C(n, 2) + d_r + d_s + 1 + 2n²` changes (`d_r`, `d_s` asserted pairs,
    diagonal included), `1 + 2n²` of them additions; on a part asserting no
    loop, `n` plus its related pairs make some loop asserted in that relation
    (the eighth's count on each part).  The empty state has one change, an
    addition.
    """
    n = state.n
    total, xrx, xsx = attempt_counts_eighth(state)
    return total, 1 + 2 * n * n, xrx, xsx
