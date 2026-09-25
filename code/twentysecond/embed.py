"""The seventh's states in, the map back, and the ninth's results merged.

Derived (paper; `lean4_core/Twentysecond/Seventh.lean`, `Rename.lean`)
    * A seventh state (one relation, `seventh.state`) read as a state
      asserting nothing with `s` (`ninth.state.of_r`) is its own plain state,
      so two seventh states give the same result here exactly when they are
      the same seventh result (`embed`), and each seventh change is carried
      to a change of the same kind.
    * The map back (`read_back`) reads a result's plain state: its `r` part
      (least writing) if it asserts nothing with `s`, "none" (`None`)
      otherwise.  It returns the original on every embedded seventh result;
      the first result it answers "none" on, in round order, is the one-term
      result asserting `asa` once (`smallest_none`).
    * The ninth's states do not map one to one: two ninth results are one
      result here when their plain states are the same (`ninth_image`).

Cited from the seventh and ninth derivations and re-checked (computed again)
    `seventh.explore` (`explore`, `count_shortest_sequences`) and
    `ninth.explore.explore` are run beside this seed's exploration in
    `twentysecond.evidence`; `fourth.state.canonical` is the seventh's least
    writing.
"""

from __future__ import annotations

from fourth.state import canonical as canonical_part

from twentysecond.explore import Exploration, order
from twentysecond.state import DState, MState, of_r, plain, result_of

__all__ = ["embed", "ninth_image", "read_back", "smallest_none"]


def embed(part: MState) -> DState:
    """The result of a seventh state read as asserting nothing with `s`."""
    return result_of(of_r(part))


def read_back(state: DState) -> MState | None:
    """The seventh result a result comes from: its plain state's `r` part, or `None` if it asserts something with `s`."""
    p = plain(state)
    if p.total_s:
        return None
    return canonical_part(MState(p.n, p.r, None))


def smallest_none(expl: Exploration) -> DState | None:
    """The first result, in round then fixed order, that the map back answers "none" on."""
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if read_back(state) is None:
            return state
    return None


def ninth_image(state: DState) -> DState:
    """The result here of a ninth state (its plain state's least writing)."""
    return result_of(state)
