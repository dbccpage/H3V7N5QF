"""Whether a state asserts some `xrx`, and the two readings of "makes".

Given
    A change that makes some `xrx` asserted is obstructed. The ban "for no
    term `x` may `xrx` be asserted" is not in this seed.

Cited from the base and re-checked
    `xry.changes.obstruction` is M1: the assertions that would become `xrx`.
    `State.legal` is the predicate "no `xrx`", no longer a given.

Chosen
    M2: the change is obstructed when its outcome asserts some `xrx`.
"""

from __future__ import annotations

from xry.changes import Change, changes, obstruction, perform
from xry.state import State


def has_xrx(state: State) -> bool:
    """Does `state` assert some `xrx`?"""
    return bool(state.loops)


def obstructed_m1(state: State, change: Change) -> bool:
    """M1: the base obstruction is non-empty."""
    return bool(obstruction(state, change))


def outcome_has_xrx(state: State, change: Change) -> bool:
    """M2: `perform` of `change` asserts some `xrx`."""
    return has_xrx(perform(state, change))


def readings_agree(state: State) -> bool:
    """Do M1 and M2 name the same changes of `state`?"""
    return all(
        obstructed_m1(state, change) == outcome_has_xrx(state, change) for change in changes(state)
    )
