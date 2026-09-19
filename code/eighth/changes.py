"""Changes of the eighth seed: the sixth's four kinds over two relations, every one performed.

Given by the eighth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Nothing else is a change.  Adding an
    assertion raises its multiplicity by one; removing lowers it by one.
    Identifying two terms replaces both by one term in every assertion — of
    either relation.  Nothing is forbidden.

Cited from the first, fourth, fifth and sixth derivations and re-checked
    `Kind` (the four kinds) mentions no relation and survives.  The sixth's
    `changes` listed one relation's pairs; the list is written again with
    both.  `fourth.changes.perform` (a term; an assertion) and the fifth's
    `remove`, `identify` act on one projection and are used through the
    parts (`eighth.state`).  The sixth's `attempt_counts` gives, on each
    part, the number of changes of that part making some `xrx` (or `xsx`)
    asserted; it survives per relation and is imported.

Derived (paper, `lean4/Eighth/`)
    * A result with `n` terms and `d_r + d_s` asserted pairs (diagonal pairs
      included) has `C(n, 2) + d_r + d_s + 1 + 2n²` changes, every one
      performed.
    * On a result asserting no `xrx`, `n` plus the related pairs in `r` of
      its changes make some `xrx` asserted (the sixth's count on the `r`
      part); likewise for `s`.

Chosen here (readings C5⁗ and C6 of the paper)
    * Removing what is not asserted, and identifying a term with itself,
      change nothing and are not changes; adding what is asserted is a change.
    * An identification adds up the multiplicities of the merged pairs in
      each relation separately.
    * Fewest additions first: identifications, removals in `r`, removals in
      `s` (no addition), then a term, then the additions in `r`, then in `s`
      — the seed's order of kinds and of relations among equals.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from fourth.changes import Change as ChangePart
from fourth.changes import perform as perform_part
from sixth.changes import attempt_counts as attempt_counts_part
from xry.changes import Kind

from eighth.state import RELATIONS, DState, identify, pair, remove

__all__ = ["KINDS", "RELATIONS", "Change", "Kind", "attempt_counts", "changes", "is_change", "makes_some_loop", "perform"]

#: The four kinds of change, in the seed's order.
KINDS: tuple[Kind, ...] = (Kind.IDENTIFY, Kind.REMOVE, Kind.ADD_TERM, Kind.ADD_ASSERTION)


@dataclass(frozen=True)
class Change:
    """One change.  `rel` is the relation of an assertion added or removed; `x`, `y` the terms it mentions."""

    kind: Kind
    rel: str = ""
    x: int = -1
    y: int = -1

    def __post_init__(self) -> None:
        if self.kind in (Kind.REMOVE, Kind.ADD_ASSERTION) and self.rel not in RELATIONS:
            raise ValueError("an assertion is written with r or with s")
        if self.kind in (Kind.IDENTIFY, Kind.ADD_TERM) and self.rel:
            raise ValueError("a term or an identification mentions no relation")

    @property
    def additions(self) -> tuple[int, int]:
        """(terms, assertions) this change adds."""
        if self.kind is Kind.ADD_TERM:
            return (1, 0)
        if self.kind is Kind.ADD_ASSERTION:
            return (0, 1)
        return (0, 0)

    def part(self) -> ChangePart:
        """The same change read on one relation's part (the fourth's / fifth's record)."""
        return ChangePart(self.kind, self.x, self.y)

    def written(self, state: DState) -> str:
        """The change in words, using the state's writing of its terms."""
        if self.kind is Kind.ADD_TERM:
            return "add a term"
        w = state.term_writing()
        if self.kind is Kind.IDENTIFY:
            return f"identify {w[self.x]} and {w[self.y]}"
        verb = "remove" if self.kind is Kind.REMOVE else "add"
        return f"{verb} {w[self.x]}{self.rel}{w[self.y]}"


def is_change(change: Change) -> bool:
    """Is `change` one of the four kinds?"""
    return change.kind in KINDS


def changes(state: DState) -> tuple[Change, ...]:
    """Every change of the eighth seed on `state`, fewest additions first.

    Identifications (each unordered pair of terms once), removals in `r` then
    in `s` (each asserted pair once), a term, then every ordered pair as an
    addition in `r` then in `s`, asserted already or not, diagonal pairs
    included.
    """
    n = state.n
    out = [Change(Kind.IDENTIFY, "", x, y) for x in range(n) for y in range(x + 1, n)]
    for rel in RELATIONS:
        out += [Change(Kind.REMOVE, rel, x, y) for x, y in state.part(rel).pairs]
    out.append(Change(Kind.ADD_TERM))
    for rel in RELATIONS:
        out += [Change(Kind.ADD_ASSERTION, rel, x, y) for x in range(n) for y in range(n)]
    return tuple(out)


def attempt_counts(state: DState) -> tuple[int, int, int]:
    """How many changes `state` has; how many make some `xrx` asserted; how many make some `xsx` asserted.

    `C(n, 2) + d_r + d_s + 1 + 2n²` changes; on a part asserting no loop, `n`
    plus its related pairs (the sixth's count on that part), else zero.
    """
    n = state.n
    total = comb(n, 2) + state.distinct + 1 + 2 * n * n
    return total, attempt_counts_part(state.r_part())[1], attempt_counts_part(state.s_part())[1]


def perform(state: DState, change: Change) -> DState:
    """The outcome of `change`."""
    if change.kind is Kind.IDENTIFY:
        return identify(state, change.x, change.y)
    if change.kind is Kind.REMOVE:
        return remove(state, change.rel, change.x, change.y)
    if change.kind is Kind.ADD_TERM:
        return pair(perform_part(state.r_part(), change.part()), perform_part(state.s_part(), change.part()))
    if change.rel == "r":
        return pair(perform_part(state.r_part(), change.part()), state.s_part())
    return pair(state.r_part(), perform_part(state.s_part(), change.part()))


def makes_some_loop(state: DState, change: Change, rel: str) -> bool:
    """Does `change` make some `xrx` (or `xsx`) asserted, on a state asserting none in that relation?"""
    before = state.legal_r if rel == "r" else state.legal_s
    out = perform(state, change)
    after = out.legal_r if rel == "r" else out.legal_s
    return before and not after
