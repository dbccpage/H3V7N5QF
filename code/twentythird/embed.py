"""The earlier seeds mapped in, what the merge loses, and the map back.

Derived (paper, D8; `lean4_core/Twentythird/Map.lean`)
    * No earlier seed of the line maps its states one to one into this seed's
      results.  `a b; arb arb` and `a b; arb bra` are two seventh results (one
      relation), two ninth states and two twenty-second results, and one
      result here: raise `a` in the second, then take out `bra bsa`
      (`seventh_pair`).  The first seed's states (one relation, each pair at
      most once, no `xrx`, names `a`, `b`) do not either: `a b c; arb arc` and
      `a b c; bra cra` differ in every writing (in the first a term is the
      left term of two pairs, in the second none is) and are one result here,
      the first being the second raised at `a` (`first_pair`).
    * The map back (`read_back`) goes to the twenty-second's results: the
      result's state asserting the fewest when there is exactly one up to
      writing, "none" (`None`) otherwise.  On a twenty-second result mapped in
      it returns that result exactly when it is the only state of its result
      asserting the fewest; it answers another twenty-second result, or
      "none", on the others (`returns_on_mapped`).  The first result it
      answers "none" on has cost 4 (`smallest_none`).

Cited from the seventh derivation (`seventh.explore`, `seventh.state`) and
re-checked (computed again)
    The seventh's exploration is run at the same bounds and its results mapped
    in by `of_r` (the ninth's reading of a seventh state as asserting nothing
    with `s`): how many of them merge here, and the first merge in round order.
"""

from __future__ import annotations

from dataclasses import dataclass

from fourth.state import canonical as canonical_part
from seventh.explore import explore as explore_seventh
from seventh.state import empty as empty_seventh
from twentysecond.state import MState, of_r

from twentythird.cost import fewest_states
from twentythird.explore import Grouped
from twentythird.state import DState, Key, canonical, result_key

__all__ = [
    "Merges",
    "canonical_seventh",
    "first_pair",
    "order_part",
    "read_back",
    "read_back_direct",
    "returns_on_mapped",
    "seventh_merges",
    "seventh_pair",
    "smallest_none",
]


def seventh_pair() -> tuple[MState, MState]:
    """`a b; arb arb` and `a b; arb bra`: two seventh results (and ninth states, twenty-second results)."""
    return MState.of(2, [(0, 1), (0, 1)]), MState.of(2, [(0, 1), (1, 0)])


def first_pair() -> tuple[MState, MState]:
    """`a b c; arb arc` and `a b c; bra cra`: two states of the first seed, one relation, no loops."""
    return MState.of(3, [(0, 1), (0, 2)]), MState.of(3, [(1, 0), (2, 0)])


def read_back(grouped: Grouped, key: Key) -> DState | None:
    """The map back: the result's one state asserting the fewest, up to writing, or `None`."""
    fewest = grouped.fewest_members(key)
    return fewest[0] if len(fewest) == 1 else None


def read_back_direct(state: DState) -> DState | None:
    """The map back computed from one state, without the exploration: its result's states asserting the
    fewest, found by raising sets of terms, up to writing."""
    found = {canonical(f) for f in fewest_states(state)}
    return next(iter(found)) if len(found) == 1 else None


def smallest_none(grouped: Grouped) -> Key | None:
    """The first result, in round then fixed order, that the map back answers "none" on."""
    for key in grouped.ordered_keys():
        if read_back(grouped, key) is None:
            return key
    return None


def returns_on_mapped(grouped: Grouped) -> dict[str, int]:
    """On every twenty-second result reached, mapped in: does the map back return it, another, or none?"""
    out = {"returns_the_original": 0, "returns_another": 0, "answers_none": 0}
    for key, members in grouped.members.items():
        back = read_back(grouped, key)
        for m in members:
            if back is None:
                out["answers_none"] += 1
            elif back == m:
                out["returns_the_original"] += 1
            else:
                out["returns_another"] += 1
    return out


@dataclass(frozen=True)
class Merges:
    """The seventh's results mapped in: how many, into how many results, and the first merge."""

    seventh_results: int
    results_here: int
    largest_merge: int
    first_merge: tuple[MState, MState] | None
    first_merge_round: int | None


def seventh_merges(bound: int, rounds: int) -> Merges:
    """Map the seventh's results within the bound in, and find where two of them become one result."""
    seventh = explore_seventh(empty_seventh(), bound, rounds)
    by_key: dict[Key, list[MState]] = {}
    for m in sorted(seventh.depth, key=lambda s: (seventh.depth[s], order_part(s))):
        by_key.setdefault(result_key(of_r(m)), []).append(m)
    first: tuple[MState, MState] | None = None
    first_round: int | None = None
    for m in sorted(seventh.depth, key=lambda s: (seventh.depth[s], order_part(s))):
        group = by_key[result_key(of_r(m))]
        if len(group) > 1 and group[0] != m:
            first = (group[0], m)
            first_round = seventh.depth[m]
            break
    return Merges(
        seventh_results=len(seventh.depth),
        results_here=len(by_key),
        largest_merge=max((len(v) for v in by_key.values()), default=0),
        first_merge=first,
        first_merge_round=first_round,
    )


def order_part(state: MState) -> tuple[int, tuple[int, ...]]:
    """A fixed order on one-relation states."""
    return (state.n, state.mult)


def canonical_seventh(state: MState) -> MState:
    """The seventh's least writing (one relation)."""
    return canonical_part(state)
