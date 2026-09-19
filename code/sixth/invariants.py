"""What a change of the sixth seed keeps, and what it no longer keeps.

Derived (paper, `lean4/Sixth/Cost.lean`, `Step.lean`)
    Along one change the cost (size plus twice the destroyed givens, with the
    sixth seed's destroyed givens) rises by at most one
    (`cost_rises_by_at_most_one`); the names, once one term, stay one term
    (`names_stay_merged`); well-formedness and at least one term are kept.

Refuted (witnesses in `sixth.evidence`)
    The fifth's "every result asserts no `xrx`" falls: a change can make some
    `xrx` asserted (`lowered` reports it as `no_xrx`).  The fourth's counts
    that never decreased — terms, every multiplicity, the total, the size,
    the fewest classes of a split — can decrease, as under the fifth.

Cited from the fourth and fifth derivations (`fourth.invariants`) and re-checked
    `fewest_classes` is a function of a state asserting no `xrx` (a term
    related to itself fits in no class) and is compared only between such
    states; `never_decreases` is a test on a pair of states; both mention no
    change and survive as functions.
"""

from __future__ import annotations

from fourth.invariants import fewest_classes, never_decreases

from sixth.cost import cost
from sixth.state import MState, names_one_term

__all__ = ["cost_rises_by_at_most_one", "fewest_classes", "lowered", "names_stay_merged", "never_decreases"]


def cost_rises_by_at_most_one(state: MState, out: MState, bra: bool) -> bool:
    """Is the cost of `out` at most the cost of `state` plus one (both being results)?"""
    before, after = cost(state, bra), cost(out, bra)
    return before is not None and after is not None and after <= before + 1


def names_stay_merged(state: MState, out: MState) -> bool:
    """If `a` and `b` are one term in `state`, are they one term in `out`?"""
    return not names_one_term(state) or names_one_term(out)


def lowered(state: MState, out: MState) -> tuple[str, ...]:
    """Which of the earlier derivations' kept counts and properties `out` has below `state`."""
    found = []
    if out.n < state.n:
        found.append("terms")
    if out.m < state.m:
        found.append("total_multiplicity")
    if out.n == state.n and any(out.mult_of(x, y) < k for x, y, k in state.counted):
        found.append("a_multiplicity")
    if out.size < state.size:
        found.append("size")
    if state.legal and out.legal and fewest_classes(out) < fewest_classes(state):
        found.append("fewest_classes")
    if state.legal and not out.legal:
        found.append("no_xrx")
    return tuple(found)
