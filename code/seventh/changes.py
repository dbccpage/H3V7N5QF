"""Changes of the seventh seed: the sixth's four kinds, from a state that may be empty.

Given by the seventh seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Nothing else is a change.  Adding an
    assertion raises its multiplicity by one; removing lowers it by one.
    Identifying two terms replaces both by one term in every assertion.
    Nothing is forbidden.

Cited from the fifth and sixth derivations (`fifth.changes`, `sixth.changes`)
and re-checked
    `Change`, `KINDS`, `is_change`, `changes` (identifications, removals, a
    term, every ordered pair as an addition — fewest additions first) and
    `perform` mention no name and no given: they survive and are imported.
    On the empty state `changes` lists "add a term" alone, which is the
    seed's own remark that the first change can only add a term.
    `makes_some_xrx` and `related_pairs` are functions of a state and a
    change and survive.  The sixth's `attempt_counts` is written again with
    the same formula (it is stated here for `n = 0` too: one change).

Derived (paper, `lean4/Seventh/Step.lean`)
    * A result with `n` terms and `d` asserted pairs (diagonal pairs
      included) has `C(n, 2) + d + 1 + n²` changes, `1 + n²` of them
      additions; the empty state has one change, adding a term.
    * A change on a state with a term leaves a state with a term.

Chosen here (reading C5‴ of the sixth paper, restated)
    * Removing what is not asserted, and identifying a term with itself,
      change nothing and are not changes; adding what is asserted is a change.
    * An identification adds up the multiplicities of the pairs that become
      one pair.
    * Fewest additions first: identifications and removals (no addition),
      then a term, then the assertions — the seed's order among equals.
"""

from __future__ import annotations

from math import comb

from fifth.changes import KINDS, Change, Kind, changes, is_change, perform
from sixth.changes import makes_some_xrx, related_pairs

from seventh.state import MState, empty

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "first_changes",
    "is_addition",
    "is_change",
    "makes_some_xrx",
    "perform",
    "related_pairs",
]


def is_addition(change: Change) -> bool:
    """Does `change` add a term or an assertion?"""
    return change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)


def first_changes() -> tuple[Change, ...]:
    """The changes of the empty state: adding a term, and nothing else."""
    return changes(empty())


def attempt_counts(state: MState) -> tuple[int, int]:
    """How many changes `state` has, and how many of them are additions.

    `C(n, 2) + d + 1 + n²` changes (`d` asserted pairs, diagonal included),
    `1 + n²` of them additions.  The empty state has one change, an addition.
    """
    n = state.n
    return comb(n, 2) + state.distinct + 1 + n * n, 1 + n * n
