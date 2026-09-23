"""Checks that the feedback behaves as declared, on every change within a bound.

Derived (paper, `lean4/Sixteenth/`)
    Every change moves the potential by exactly one, up for a direct
    addition or a removal, down for an admission or an identification; the
    round of every result is its potential.  Neither the mass nor its
    diagonal part ever falls.  Removing an assertion and admitting its
    leftover into the same relation is the identity on the state; admitting
    it into the other relation gives a result different from the start and
    from removing then adding directly.  An admission leaves nothing; the
    leftover writing of a change of the four kinds is the fourteenth's; an
    unadmitted leftover is not an assertion; the admissions listed on a
    state are exactly two per recorded pair.

Each field of `RecordCheck` below a counter is a disagreement list, empty on
correct code, driven by an injection test and by a mutation in the sixteenth
panel of `ci/check_mutation_bite.py`.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from fourteenth.leftover import leftover_of as leftover_of_fourteenth
from ninth.changes import Kind

from sixteenth.changes import Change16, changes16, raises_potential
from sixteenth.cost import diag_mass, mass, potential
from sixteenth.explore import Exploration16, performed16
from sixteenth.leftover import leftover_of16, other_relation
from sixteenth.state import RState, add_assertion16, admit16, canonical16

__all__ = ["RecordCheck", "check_records"]


@dataclass
class RecordCheck:
    """What `check_records` records.  Disagreement lists are empty on correct code."""

    checked: int = 0
    raised: int = 0
    lowered: int = 0
    admissions: int = 0
    removals: int = 0
    potential_not_moved_by_one: list[str] = field(default_factory=list)
    direction_mismatch: list[str] = field(default_factory=list)
    mass_fell: list[str] = field(default_factory=list)
    diagonal_mass_fell: list[str] = field(default_factory=list)
    same_relation_not_identity: list[str] = field(default_factory=list)
    other_relation_same_as_start: list[str] = field(default_factory=list)
    other_relation_same_as_direct: list[str] = field(default_factory=list)
    admission_left_something: list[str] = field(default_factory=list)
    writing_not_the_fourteenth: list[str] = field(default_factory=list)
    unadmitted_asserted: list[str] = field(default_factory=list)
    admissions_not_recorded: list[str] = field(default_factory=list)
    round_not_potential: list[str] = field(default_factory=list)


def _admissions_listed_wrongly(rs: RState) -> bool:
    """Are the admissions listed on `rs` anything but two per recorded pair, each of a recorded pair?"""
    listed = [c for c in changes16(rs) if c.admits]
    for c in listed:
        if not (0 <= c.x < rs.n and 0 <= c.y < rs.n) or not rs.has_leftover(c.x, c.y):
            return True
    return len(listed) != 2 * len(rs.recorded_pairs)


def check_records(expl: Exploration16) -> RecordCheck:
    """Check every performed change within the bound, and every result's round, recording disagreements."""
    out = RecordCheck()
    seen: set[RState] = set()
    for rs, change, raw, _least in performed16(expl):
        out.checked += 1
        written = f"{rs.key()} {change.written(rs)}"
        step = potential(raw) - potential(rs)
        if abs(step) != 1:
            out.potential_not_moved_by_one.append(written)
        if (step > 0) != raises_potential(change):
            out.direction_mismatch.append(written)
        if step > 0:
            out.raised += 1
        else:
            out.lowered += 1
        if mass(raw) < mass(rs):
            out.mass_fell.append(written)
        if diag_mass(raw) < diag_mass(rs):
            out.diagonal_mass_fell.append(written)
        writing = leftover_of16(rs, change)
        if change.admits:
            out.admissions += 1
            if writing.kind != "nothing":
                out.admission_left_something.append(written)
        elif writing != leftover_of_fourteenth(rs.state, change.ninth()):
            out.writing_not_the_fourteenth.append(written)
        if writing.is_assertion():
            out.unadmitted_asserted.append(written)
        if change.kind is Kind.REMOVE:
            out.removals += 1
            # The identity: the leftover just recorded, admitted back into the same relation.
            back = admit16(raw, change.rel, change.x, change.y)
            if back != rs:
                out.same_relation_not_identity.append(written)
            # The other relation: a different result from the start, and from the direct addition.
            other = other_relation(change.rel)
            crossed = canonical16(admit16(raw, other, change.x, change.y))
            if crossed == canonical16(rs):
                out.other_relation_same_as_start.append(written)
            if crossed == canonical16(add_assertion16(raw, other, change.x, change.y)):
                out.other_relation_same_as_direct.append(written)
        if rs not in seen:
            seen.add(rs)
            if _admissions_listed_wrongly(rs):
                out.admissions_not_recorded.append(rs.key())
    for rs, round_ in expl.depth.items():
        if round_ != potential(rs):
            out.round_not_potential.append(rs.key())
    return out
