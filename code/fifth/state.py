"""Counted states under the fifth seed: the fourth's, plus removal and identification.

Given by the fifth seed
    Terms are written with letters.  An assertion `xry` is asserted a number
    of times, its multiplicity; adding raises it by one, removing lowers it by
    one.  `arb` is asserted with multiplicity one.  For no term `x` may `xrx`
    be asserted.  Whether `bra` is asserted is not given.  Identifying two
    terms replaces both by one term in every assertion.  Two results that
    differ only in how their terms are written are the same result.

Cited from the fourth derivation (`fourth.state`) and re-checked
    The counted state `MState`, its sameness under both readings
    (`canonical`, `same`, `rewrite`), the support and the indicator, what is
    given and `added` mention no change; they survive removal and
    identification unchanged and are imported.

Cited from the first derivation (`xry.changes.identification_map`) and re-checked
    Where each written term goes when two are replaced by one is a function
    of the writing alone; it survives.

Defined here
    `remove` (lowers one multiplicity by one; removing what is not asserted
    is not a change), `identify` (the multiplicities of the pairs that become
    one pair add up — the reading chosen in the paper, C5″; the fourth's
    `image` does exactly this), `names_one_term`.
"""

from __future__ import annotations

from fourth.changes import image
from fourth.state import _CANONICAL
from fourth.state import (
    GIVEN_ASSERTIONS,
    GIVEN_TERMS,
    MState,
    Names,
    Pair,
    Sameness,
    added,
    canonical,
    given,
    of_state,
    rewrite,
    same,
    support,
)
from xry.changes import identification_map

__all__ = [
    "GIVEN_ASSERTIONS",
    "GIVEN_TERMS",
    "MState",
    "Names",
    "Pair",
    "Sameness",
    "added",
    "canonical",
    "forget_canonical_forms",
    "given",
    "identification_map",
    "identify",
    "names_one_term",
    "of_state",
    "remove",
    "rewrite",
    "same",
    "support",
]


def remove(state: MState, x: int, y: int) -> MState:
    """The state with the multiplicity of `xry` lowered by one."""
    n = state.n
    if not (0 <= x < n and 0 <= y < n):
        raise ValueError("an assertion is between terms that are there")
    if not state.has(x, y):
        raise ValueError("removing what is not asserted is not a change")
    mult = list(state.mult)
    mult[x * n + y] -= 1
    return MState(n, tuple(mult), state.names)


def identify(state: MState, x: int, y: int) -> MState:
    """The state with the terms `x < y` replaced by one term (written `x`) in every assertion.

    The multiplicities of the pairs that become one pair add up.  The names
    follow their terms.  The outcome may be illegal (some `xrx` asserted).
    """
    q = identification_map(state.n, x, y)
    names = None if state.names is None else (q[state.names[0]], q[state.names[1]])
    return image(state, q, state.n - 1, names)


def names_one_term(state: MState) -> bool:
    """Are the names `a` and `b` carried by one term?  (False without names.)"""
    return state.names is not None and state.names[0] == state.names[1]


def forget_canonical_forms() -> int:
    """Empty the cache of least writings (`fourth.state`); returns how many it held.

    The cache is an optimisation only; emptying it between explorations keeps
    the memory of a long run bounded and changes no result.
    """
    held = len(_CANONICAL)
    _CANONICAL.clear()
    return held
