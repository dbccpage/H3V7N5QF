"""Changes of the sixteenth seed: the ninth's four kinds on a state with a record, and the admission.

Given by the sixteenth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Nothing else is a change.  A
    recorded leftover `xℓy` may be admitted, adding the assertion `xry` or
    the assertion `xsy`.  Attempt every change, fewest additions first.

Cited from the ninth derivation (`ninth.changes`, `eighth.changes`) and re-checked
    `Kind`, `Change` (the record of one change of the four kinds), `changes`
    (the list on a ninth state) and `perform` mention no record; every
    change of the four kinds on a ninth state is a change of the sixteenth
    on the state with any record, and its outcome on the state part is the
    ninth's.  They are imported and act on the state part; what each does to
    the record is defined in `sixteenth.state`.

Chosen here (C-R1)
    * An admission is a change: it adds an assertion (one of the four kinds),
      performed by admitting a recorded leftover rather than directly.  A
      leftover names no relation, so a recorded `xℓy` may be admitted into
      `r` or into `s`.  Admitting consumes the leftover.
    * The order, fewest additions first: identifications, removals in `r`,
      in `s`, a term, the direct additions in `r`, in `s`, then the
      admissions in `r`, in `s` (each recorded pair once per relation).  The
      order fixes the attempt log only; the results and their rounds do not
      depend on it.

Derived (paper)
    A state with `n` terms, `d_r + d_s` asserted pairs and `d_ℓ` recorded
    pairs has `C(n, 2) + d_r + d_s + 1 + 2n² + 2·d_ℓ` changes, `1 + 2n²` of
    them direct additions and `2·d_ℓ` admissions.  The empty state has one
    change, adding a term.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from eighth.changes import RELATIONS
from ninth.changes import Change as NinthChange
from ninth.changes import Kind, changes as changes_ninth

from sixteenth.state import RState, Reading, add_assertion16, add_term16, admit16, empty16, identify16, remove16

__all__ = [
    "KINDS",
    "RELATIONS",
    "Change16",
    "Kind",
    "admissions_of",
    "attempt_counts16",
    "changes16",
    "first_changes16",
    "is_addition16",
    "is_admission",
    "is_direct_addition",
    "perform16",
    "raises_potential",
]

#: The four kinds of change, in the seed's order (an admission is of the fourth kind).
KINDS: tuple[Kind, ...] = (Kind.IDENTIFY, Kind.REMOVE, Kind.ADD_TERM, Kind.ADD_ASSERTION)


@dataclass(frozen=True)
class Change16:
    """One change.  `admits` marks an assertion added by admitting a recorded leftover of its pair."""

    kind: Kind
    rel: str = ""
    x: int = -1
    y: int = -1
    admits: bool = False

    def __post_init__(self) -> None:
        if self.kind in (Kind.REMOVE, Kind.ADD_ASSERTION) and self.rel not in RELATIONS:
            raise ValueError("an assertion is written with r or with s")
        if self.kind in (Kind.IDENTIFY, Kind.ADD_TERM) and self.rel:
            raise ValueError("a term or an identification mentions no relation")
        if self.admits and self.kind is not Kind.ADD_ASSERTION:
            raise ValueError("only an assertion is added by admitting a leftover")

    @property
    def additions(self) -> tuple[int, int]:
        """(terms, assertions) this change adds; an admission adds one assertion."""
        if self.kind is Kind.ADD_TERM:
            return (1, 0)
        if self.kind is Kind.ADD_ASSERTION:
            return (0, 1)
        return (0, 0)

    def ninth(self) -> NinthChange:
        """The same change on the ninth state: an admission projects to the direct addition."""
        return NinthChange(self.kind, self.rel, self.x, self.y)

    def written(self, rs: RState) -> str:
        """The change in words, using the state's writing of its terms."""
        if self.admits:
            w = rs.state.term_writing()
            return f"admit {w[self.x]}ℓ{w[self.y]} into {self.rel}"
        return self.ninth().written(rs.state)


def is_addition16(change: Change16) -> bool:
    """Does `change` add a term or an assertion (directly or by admission)?"""
    return change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)


def is_admission(change: Change16) -> bool:
    """Is `change` an admission of a recorded leftover?"""
    return change.admits


def is_direct_addition(change: Change16) -> bool:
    """Does `change` add a term, or an assertion directly (not by admission)?"""
    return is_addition16(change) and not change.admits


def raises_potential(change: Change16) -> bool:
    """Does `change` raise the potential by one?  The direct additions and the removals do; admissions and identifications lower it."""
    return is_direct_addition(change) or change.kind is Kind.REMOVE


def admissions_of(x: int, y: int) -> tuple[Change16, ...]:
    """The two admissions of a recorded `xℓy`: into `r`, then into `s`."""
    return tuple(Change16(Kind.ADD_ASSERTION, rel, x, y, True) for rel in RELATIONS)


def changes16(rs: RState) -> tuple[Change16, ...]:
    """Every change on `rs`, fewest additions first: the ninth's list on the state, then the admissions."""
    out = [Change16(c.kind, c.rel, c.x, c.y) for c in changes_ninth(rs.state)]
    for rel in RELATIONS:
        out += [Change16(Kind.ADD_ASSERTION, rel, x, y, True) for x, y in rs.recorded_pairs]
    return tuple(out)


def first_changes16() -> tuple[Change16, ...]:
    """The changes of the empty state: adding a term, and nothing else."""
    return changes16(empty16())


def attempt_counts16(rs: RState) -> tuple[int, int, int]:
    """How many changes `rs` has; how many are direct additions; how many are admissions.

    `C(n, 2) + d_r + d_s + 1 + 2n² + 2·d_ℓ`, `1 + 2n²`, `2·d_ℓ`.
    """
    n = rs.n
    recorded = rs.record.distinct
    return comb(n, 2) + rs.state.distinct + 1 + 2 * n * n + 2 * recorded, 1 + 2 * n * n, 2 * recorded


def perform16(rs: RState, change: Change16, reading: Reading = Reading.COUNT) -> RState:
    """The outcome of `change` on `rs` under the chosen reading (or an unchosen one)."""
    if change.kind is Kind.IDENTIFY:
        return identify16(rs, change.x, change.y, reading)
    if change.kind is Kind.REMOVE:
        return remove16(rs, change.rel, change.x, change.y, reading)
    if change.kind is Kind.ADD_TERM:
        return add_term16(rs)
    if change.admits:
        return admit16(rs, change.rel, change.x, change.y)
    return add_assertion16(rs, change.rel, change.x, change.y)
