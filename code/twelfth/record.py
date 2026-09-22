"""Per-relation identification records of the twelfth seed.

Given by the twelfth seed
    Identifying two terms records, for each relation, which assertions of
    those two terms become one assertion.  The record is kept with the
    result.

Chosen here (reading C-M1 of the paper)
    The record of identifying `x < y` in one relation is the grouping of
    asserted pairs that mention either term, by the pair they become under
    the identification map.  It is computed from the start and the two
    terms, not stored as a third multiplicity.  "Assertions of those two
    terms" is read as every asserted pair among `{x, y}` (the 2×2 block,
    all becoming the merged loop) together with, for each other term `z`,
    the outgoing pair `(xz, yz)` becoming one pair and the incoming pair
    `(zx, zy)` becoming one pair.  Only pairs with positive multiplicity
    are listed.  Other terms are remembered only by the pattern of which
    of the two pairs were asserted, sorted, so the record is invariant
    under rewriting the other terms.

Cited from the ninth derivation (`ninth.state`, `ninth.changes`) and re-checked
    `perform`, `identify` and `same` mention no record: they survive and
    are imported.  The record is not a third multiplicity beside `r` and
    `s` (the state is the ninth's).
"""

from __future__ import annotations

from dataclasses import dataclass

from ninth.changes import Change, Kind, changes, perform
from ninth.state import RELATIONS, DState, same

__all__ = [
    "LOOP_TAGS",
    "IdentRecord",
    "RelRecord",
    "became_one",
    "empty_rel",
    "other_relation",
    "record_determined_by_rel",
    "record_of",
    "record_rel",
    "restores_listed",
    "zero_relation",
]

LOOP_TAGS: tuple[str, ...] = ("xx", "xy", "yx", "yy")


@dataclass(frozen=True, order=True)
class RelRecord:
    """Which asserted pairs of the two identified terms became one pair, in one relation."""

    loop: tuple[str, ...]
    outgoing: tuple[tuple[bool, bool], ...]
    incoming: tuple[tuple[bool, bool], ...]

    def is_empty(self) -> bool:
        """Were no assertions of this relation among the two terms asserted?"""
        return not self.loop and not self.outgoing and not self.incoming


def empty_rel() -> RelRecord:
    """The record of a relation that asserted nothing among the two terms."""
    return RelRecord((), (), ())


@dataclass(frozen=True, order=True)
class IdentRecord:
    """The pair of per-relation records of one identification."""

    r: RelRecord
    s: RelRecord

    def is_empty(self) -> bool:
        """Were no assertions of either relation among the two terms asserted?"""
        return self.r.is_empty() and self.s.is_empty()

    def swapped(self) -> IdentRecord:
        """The two relations exchanged."""
        return IdentRecord(self.s, self.r)

    def as_json(self) -> dict[str, object]:
        """A JSON-stable form."""
        return {
            "r": {"loop": list(self.r.loop), "outgoing": [list(p) for p in self.r.outgoing], "incoming": [list(p) for p in self.r.incoming]},
            "s": {"loop": list(self.s.loop), "outgoing": [list(p) for p in self.s.outgoing], "incoming": [list(p) for p in self.s.incoming]},
        }


def other_relation(rel: str) -> str:
    """The other of the two relations."""
    if rel == "r":
        return "s"
    if rel == "s":
        return "r"
    raise ValueError("an assertion is written with r or with s")


def zero_relation(state: DState, rel: str) -> DState:
    """The same terms with relation `rel` asserting nothing."""
    zeros = (0,) * (state.n * state.n)
    if rel == "r":
        return DState(state.n, zeros, state.s, state.names)
    if rel == "s":
        return DState(state.n, state.r, zeros, state.names)
    raise ValueError("an assertion is written with r or with s")


def record_rel(state: DState, rel: str, x: int, y: int) -> RelRecord:
    """The record of identifying `x < y` in one relation."""
    if rel not in RELATIONS:
        raise ValueError("an assertion is written with r or with s")
    n = state.n
    if not 0 <= x < y < n:
        raise ValueError("identifying takes two terms, written x < y")
    loop = tuple(tag for tag, (i, j) in (("xx", (x, x)), ("xy", (x, y)), ("yx", (y, x)), ("yy", (y, y))) if state.has(rel, i, j))
    outgoing: list[tuple[bool, bool]] = []
    incoming: list[tuple[bool, bool]] = []
    for z in range(n):
        if z == x or z == y:
            continue
        xz, yz = state.has(rel, x, z), state.has(rel, y, z)
        if xz or yz:
            outgoing.append((xz, yz))
        zx, zy = state.has(rel, z, x), state.has(rel, z, y)
        if zx or zy:
            incoming.append((zx, zy))
    return RelRecord(loop, tuple(sorted(outgoing)), tuple(sorted(incoming)))


def record_of(state: DState, x: int, y: int) -> IdentRecord:
    """The pair of per-relation records of identifying `x < y` on `state`."""
    return IdentRecord(record_rel(state, "r", x, y), record_rel(state, "s", x, y))


def record_determined_by_rel(state: DState, rel: str, x: int, y: int) -> bool:
    """Does the record of `rel` ignore the other relation?"""
    other = other_relation(rel)
    return record_rel(state, rel, x, y) == record_rel(zero_relation(state, other), rel, x, y)


def became_one(rec: RelRecord) -> bool:
    """Did two or more asserted pairs become one pair?"""
    return len(rec.loop) >= 2 or any(a and b for a, b in rec.outgoing) or any(a and b for a, b in rec.incoming)


def restores_listed(state: DState, change: Change) -> bool:
    """Does some one later change of the four kinds restore `state` (up to writing)?

    That is the sense in which a later change restores what the record lists:
    the listed assertions as they were, as separate assertions of two terms.
    """
    if change.kind is not Kind.IDENTIFY:
        return False
    out = perform(state, change)
    return any(same(perform(out, later), state) for later in changes(out))
