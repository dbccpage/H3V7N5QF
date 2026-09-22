"""Checks that writings determine as declared, and that a collision forbids coarser writings.

Derived (paper, `lean4/Eleventh/`)
    Every injective writing determines.  If a writing does not determine,
    neither does any coarser writing.  A collision of one relation need not
    be a collision of the other.  Identifying two terms drops a term;
    writing them the same does not.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ninth.changes import Change, Kind, perform

from eleventh.explore import Exploration, writings_of
from eleventh.writing import coarser_than, determines, determines_rel, injective, terms_after_writing

__all__ = ["WritingCheck", "check_writings"]


@dataclass
class WritingCheck:
    """What `check_writings` records.  Disagreement lists are empty on correct code."""

    checked: int = 0
    injective_writings: int = 0
    determining: int = 0
    colliding: int = 0
    r_not_s: int = 0
    injective_not_determining: list[str] = field(default_factory=list)
    coarser_of_collision_determines: list[str] = field(default_factory=list)
    identify_kept_both_terms: list[str] = field(default_factory=list)
    collide_dropped_a_term: list[str] = field(default_factory=list)


def check_writings(expl: Exploration) -> WritingCheck:
    """Classify every writing of every explored result and record disagreements."""
    out = WritingCheck()
    for state in expl.depth:
        ws = writings_of(state)
        colliding = [w for w in ws if not determines(state, w)]
        for writing in ws:
            out.checked += 1
            written = f"{state.key()} {writing}"
            if injective(writing):
                out.injective_writings += 1
                if not determines(state, writing):
                    out.injective_not_determining.append(written)
            if determines(state, writing):
                out.determining += 1
            else:
                out.colliding += 1
            if (not determines_rel(state, writing, "r")) and determines_rel(state, writing, "s"):
                out.r_not_s += 1
            if writing in colliding:
                for other in ws:
                    if coarser_than(writing, other) and determines(state, other):
                        out.coarser_of_collision_determines.append(f"{written} -> {other}")
        if state.n >= 2:
            ident = Change(Kind.IDENTIFY, "", 0, 1)
            merged = perform(state, ident)
            if merged.n != state.n - 1:
                out.identify_kept_both_terms.append(state.key())
            collide = (0,) * state.n
            if terms_after_writing(state, collide) != state.n:
                out.collide_dropped_a_term.append(state.key())
    return out
