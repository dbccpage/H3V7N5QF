"""Changes of the sixth seed: the fifth's four kinds, every one performed.

Given by the sixth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Nothing else is a change.  Adding an
    assertion raises its multiplicity by one; removing lowers it by one.
    Identifying two terms replaces both by one term in every assertion.
    Nothing is forbidden, so nothing is obstructed, answered, refused or
    built.

Cited from the fifth derivation (`fifth.changes`) and re-checked
    `Change` (the record of one change), `KINDS`, `is_change`, `changes` (the
    list of changes of a state, fewest additions first: identifications,
    removals, a term, every ordered pair as an addition — `xrx` included, as
    the fifth already listed it) and `perform` (the outcome of a change) look
    at no legality: the fifth attempted every change and refused the
    obstructed ones *after* listing them.  They survive and are imported.
    The fifth's `obstruction`, `answers`, `is_build_of`, `one_term_builds`
    and `REMOVAL_IS_REFUSAL` are not imported: the sixth seed has nothing
    they are about.

Derived (paper, `lean4/Sixth/`)
    * A result with `n` terms and `d` asserted pairs (diagonal pairs
      included) has `C(n, 2) + d + 1 + n²` changes, every one performed.
    * A change makes some `xrx` asserted, on a state asserting none, exactly
      when it adds some `xrx` or identifies two related terms (the fifth's
      obstruction characterisation, now a fact about the outcome): `n` plus
      the number of related pairs of the changes of such a state.

Chosen here (reading C5″ of the paper, restated)
    * Removing what is not asserted, and identifying a term with itself,
      change nothing and are not changes; adding what is asserted is a change.
    * An identification adds up the multiplicities of the pairs that become
      one pair; `urv`, `vru`, `uru`, `vrv` all become `uru`.
    * Fewest additions first: identifications and removals (no addition),
      then a term, then the assertions — the seed's order among equals.
"""

from __future__ import annotations

from math import comb

from fifth.changes import KINDS, Change, Kind, changes, is_change, perform

from sixth.state import MState

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "is_change",
    "makes_some_xrx",
    "perform",
    "related_pairs",
]


def makes_some_xrx(state: MState, change: Change) -> bool:
    """Does `change` make some `xrx` asserted, on a state asserting none?

    This is exactly what the fifth seed called obstructed; under the sixth
    seed it is a property of the outcome and the change is performed.
    """
    return state.legal and not perform(state, change).legal


def related_pairs(state: MState) -> int:
    """How many unordered pairs of two terms are related (`xry` or `yrx` asserted)."""
    n = state.n
    return sum(1 for x in range(n) for y in range(x + 1, n) if state.related(x, y))


def attempt_counts(state: MState) -> tuple[int, int]:
    """How many changes `state` has, and how many make some `xrx` asserted on a state asserting none.

    `C(n, 2) + d + 1 + n²` changes (`d` asserted pairs, diagonal included);
    on a state asserting no `xrx`, the `n` additions of some `xrx` and the
    identifications of related pairs make some `xrx` asserted; on a state
    asserting some `xrx` the second number is zero by definition.
    """
    n = state.n
    total = comb(n, 2) + state.distinct + 1 + n * n
    return total, (n + related_pairs(state)) if state.legal else 0
