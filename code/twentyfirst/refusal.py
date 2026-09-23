"""An obstructed change is refused, and a refusal changes nothing."""

from __future__ import annotations

from xry.state import State


def refusal_result(state: State) -> State:
    """A refused change is recorded and changes nothing."""
    return state
