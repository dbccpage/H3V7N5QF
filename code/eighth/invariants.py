"""What a change of the eighth seed keeps, and what it does not keep.

Derived (paper, `lean4/Eighth/Cost.lean`, `Step.lean`)
    Along one change the cost (the sixth's on the `r` part plus the `s`
    total) rises by at most one (`cost_rises_by_at_most_one`); the names,
    once one term, stay one term (`names_stay_merged`); well-formedness and
    at least one term are kept.

Refuted (witnesses in `eighth.evidence`)
    The counts the earlier derivations kept — terms, each relation's total,
    every multiplicity, the size, the fewest classes of a split in either
    relation, "no `xrx`", "no `xsx`" — can fall along a change (`lowered`).

Cited from the fourth and fifth derivations (`fourth.invariants`) and re-checked
    `fewest_classes` is a function of one relation's part asserting no loop;
    it survives per relation.
"""

from __future__ import annotations

from fourth.invariants import fewest_classes

from eighth.cost import cost
from eighth.state import DState, names_one_term

__all__ = ["cost_rises_by_at_most_one", "fewest_classes", "lowered", "names_stay_merged"]


def cost_rises_by_at_most_one(state: DState, out: DState, bra: bool) -> bool:
    """Is the cost of `out` at most the cost of `state` plus one (both being results)?"""
    before, after = cost(state, bra), cost(out, bra)
    return before is not None and after is not None and after <= before + 1


def names_stay_merged(state: DState, out: DState) -> bool:
    """If `a` and `b` are one term in `state`, are they one term in `out`?"""
    return not names_one_term(state) or names_one_term(out)


def lowered(state: DState, out: DState) -> tuple[str, ...]:
    """Which of the earlier derivations' kept counts and properties `out` has below `state`."""
    found = []
    if out.n < state.n:
        found.append("terms")
    if out.total_r < state.total_r:
        found.append("total_r")
    if out.total_s < state.total_s:
        found.append("total_s")
    if out.n == state.n and any(o < k for o, k in zip(out.r + out.s, state.r + state.s)):
        found.append("a_multiplicity")
    if out.size < state.size:
        found.append("size")
    for rel in ("r", "s"):
        before, after = state.part(rel), out.part(rel)
        if before.legal and after.legal and fewest_classes(after) < fewest_classes(before):
            found.append(f"fewest_classes_{rel}")
        if before.legal and not after.legal:
            found.append(f"no_x{rel}x")
    return tuple(found)
