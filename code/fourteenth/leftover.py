"""Leftover writings of a change of the fourteenth seed.

Given by the fourteenth seed
    After every change, record what that change leaves.  A leftover is
    written neither `xry` nor `xsy`.  A leftover is not an assertion and is
    not an answer.

Chosen here (reading C-F1 of the paper)
    Leftover is recorded on the change, not as a field of the result.  The
    leftover writing of a change from `S` to `T` is:

    * an addition (a term, or an assertion of either relation): nothing —
      the added thing is a term or an assertion;
    * a removal of a pair `(x, y)` in either relation: that pair, written
      `xℓy` with a third letter `ℓ` that is neither `r` nor `s`;
    * an identification of terms `u` and `v`: those two terms, written
      `u∼v`, not an assertion.

    The writing of a removal names no relation, so leftover of a removal in
    `r` of a pair is leftover of a removal in `s` of that pair.

Cited from the ninth derivation (`ninth.changes`, `ninth.state`) and re-checked
    `perform`, `changes`, `Kind` and `same` mention no leftover: they survive
    and are imported.  Leftover is not a third multiplicity beside `r` and
    `s` (the state is the ninth's).
"""

from __future__ import annotations

from dataclasses import dataclass

from ninth.changes import Change, Kind, is_addition

__all__ = [
    "LeftWriting",
    "clearing_is_a_kind",
    "leftover_merge",
    "leftover_merge_survivor",
    "leftover_nothing",
    "leftover_of",
    "leftover_pair",
    "other_relation",
]


@dataclass(frozen=True)
class LeftWriting:
    """A leftover writing: neither `xry` nor `xsy`."""

    kind: str
    x: int = -1
    y: int = -1

    def written(self) -> str:
        """The leftover in letters.  Never `xry` and never `xsy`.

        A merge writing carries the two identified terms (`u∼v`) on the change
        it records (C-F1); the canonical tag of a result (C-F2) keeps only the
        surviving term, `y = -1`, written `∼u`, because the other term is gone
        from the result and naming it would name an absent term.
        """
        if self.kind == "nothing":
            return "nothing"
        if self.kind == "pair":
            return f"{self.x}ℓ{self.y}"
        if self.kind == "merge":
            if self.y < 0:
                return f"∼{self.x}"
            return f"{self.x}∼{self.y}"
        raise ValueError("a leftover is nothing, a pair, or a merge")  # pragma: no cover

    def is_xry(self) -> bool:
        """Is this leftover written `xry`?  Never: leftover uses neither `r` nor `s`."""
        return self.kind == "pair" and "r" in self.written()

    def is_xsy(self) -> bool:
        """Is this leftover written `xsy`?  Never."""
        return self.kind == "pair" and "s" in self.written()

    def is_assertion(self) -> bool:
        """Is leftover an assertion?  The seed says it is not."""
        return self.is_xry() or self.is_xsy()

    def is_answer(self) -> bool:
        """Is leftover an answer (refuse, remove the obstruction, build)?  The seed says it is not."""
        return False

    def __str__(self) -> str:
        return self.written()


def leftover_nothing() -> LeftWriting:
    """The leftover writing of an addition: nothing."""
    return LeftWriting("nothing")


def leftover_pair(x: int, y: int) -> LeftWriting:
    """The leftover writing of a removal: the pair, no relation."""
    return LeftWriting("pair", x, y)


def leftover_merge(u: int, v: int) -> LeftWriting:
    """The leftover writing of an identification: the two terms, not an assertion."""
    return LeftWriting("merge", u, v)


def leftover_merge_survivor(u: int) -> LeftWriting:
    """The canonical merge tag of a result (C-F2): the surviving term alone, `∼u`."""
    return LeftWriting("merge", u, -1)


def other_relation(rel: str) -> str:
    """The other of the two relations."""
    if rel == "r":
        return "s"
    if rel == "s":
        return "r"
    raise ValueError("an assertion is written with r or with s")


def leftover_of(_state: object, change: Change) -> LeftWriting:
    """Which leftover writing `change` has (C-F1).  The state is unused: leftover is of the change."""
    if is_addition(change):
        return leftover_nothing()
    if change.kind is Kind.REMOVE:
        return leftover_pair(change.x, change.y)
    if change.kind is Kind.IDENTIFY:
        return leftover_merge(change.x, change.y)
    raise ValueError("nothing else is a change")  # pragma: no cover


def clearing_is_a_kind(leftover: LeftWriting) -> bool:
    """Is leftover an object of one of the four kinds?  Never: leftover is not a term and not an assertion."""
    del leftover
    return False
