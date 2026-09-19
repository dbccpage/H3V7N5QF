"""Counted states under the sixth seed: the fifth's, with `xrx` a pair like any other.

Given by the sixth seed
    Terms are written with letters.  An assertion `xry` is asserted a number
    of times, its multiplicity; adding raises it by one, removing lowers it by
    one.  `arb` is asserted with multiplicity one.  Whether `bra` is asserted
    is not given.  Identifying two terms replaces both by one term in every
    assertion.  Two results that differ only in how their terms are written
    are the same result.  Nothing forbids `xrx`.

Cited from the fourth and fifth derivations (`fourth.state`, `fifth.state`)
and re-checked
    The counted state `MState`, its sameness under both readings
    (`canonical`, `same`, `rewrite`), the support and the indicator, what is
    given, `added`, `remove`, `identify` (multiplicities of the pairs that
    become one pair add up: `urv`, `vru`, `uru`, `vrv` all become `uru`),
    `names_one_term` and the cache of least writings mention no legality;
    they survive `xrx` being allowed and are imported.  `MState.legal` is
    kept as a *property* a state may have ("no `xrx` asserted"), no longer a
    condition on results.

Defined here
    `asserts_some_xrx`, `largest_xrx` (the largest multiplicity of any `xrx`)
    and `named_xrx` (how often `crc` is asserted at the one term carrying
    both names), which the cost of a state with the names one term depends
    on.
"""

from __future__ import annotations

from fifth.state import (
    GIVEN_ASSERTIONS,
    GIVEN_TERMS,
    MState,
    Names,
    Pair,
    Sameness,
    added,
    canonical,
    forget_canonical_forms,
    given,
    identification_map,
    identify,
    names_one_term,
    of_state,
    remove,
    rewrite,
    same,
    support,
)

__all__ = [
    "GIVEN_ASSERTIONS",
    "GIVEN_TERMS",
    "MState",
    "Names",
    "Pair",
    "Sameness",
    "added",
    "asserts_some_xrx",
    "canonical",
    "forget_canonical_forms",
    "given",
    "identification_map",
    "identify",
    "largest_xrx",
    "named_xrx",
    "names_one_term",
    "of_state",
    "remove",
    "rewrite",
    "same",
    "support",
]


def asserts_some_xrx(state: MState) -> bool:
    """Is some `xrx` asserted?  (The fifth seed's "illegal"; now a property like any other.)"""
    return not state.legal


def largest_xrx(state: MState) -> int:
    """The largest multiplicity of any `xrx` (0 when none is asserted, or without terms)."""
    return max((state.mult_of(x, x) for x in range(state.n)), default=0)


def named_xrx(state: MState) -> int:
    """How often `crc` is asserted at the one term `c` carrying both names.

    Raises when the names are two terms or absent: the number is only meant
    for a state with the names one term.
    """
    if not names_one_term(state):
        raise ValueError("the names are not one term")
    assert state.names is not None
    c = state.names[0]
    return state.mult_of(c, c)
