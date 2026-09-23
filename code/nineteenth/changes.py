"""Identification rewrites one chosen assertion and leaves the terms in place.

Chosen: the two terms, the asserted pair that is rewritten, and which of the
two terms is written in that pair. A pair that does not mention either term
is not a choice. If the pair is unchanged, it is not a change. The other
three kinds are the base's.

Unchosen, kept: only a pair in which the two terms already both occur. Every
such rewrite is a loop, so every such change is obstructed.
"""

from __future__ import annotations

from dataclasses import dataclass

from xry.changes import Change, Kind, changes as base_changes
from xry.state import Pair, State


@dataclass(frozen=True)
class Partial:
    """Rewrite one asserted pair, writing `survivor` for both identified terms."""

    u: int
    v: int
    pair: Pair
    survivor: int

    def written(self, state: State) -> str:
        w = state.term_writing()
        x, y = self.pair
        return (
            f"identify {w[self.u]} and {w[self.v]} in {w[x]}r{w[y]} as {w[self.survivor]}"
        )


def _mentions(pair: Pair, u: int, v: int) -> bool:
    return pair[0] in (u, v) or pair[1] in (u, v)


def _both(pair: Pair, u: int, v: int) -> bool:
    return {pair[0], pair[1]} == {u, v}


def rewrite_pair(pair: Pair, u: int, v: int, survivor: int) -> Pair:
    """Write `survivor` in place of `u` and of `v` in this one pair."""

    def sub(term: int) -> int:
        return survivor if term in (u, v) else term

    return sub(pair[0]), sub(pair[1])


def perform_partial(state: State, partial: Partial) -> State:
    """The outcome of one partial identification. The terms stay."""
    rewritten = rewrite_pair(partial.pair, partial.u, partial.v, partial.survivor)
    pairs = [pair for pair in state.pairs if pair != partial.pair]
    pairs.append(rewritten)
    return State.of(state.n, pairs, state.names)


def partials(state: State, cooccur_only: bool = False) -> tuple[Partial, ...]:
    """Every partial identification on `state`."""
    out: list[Partial] = []
    for u in range(state.n):
        for v in range(u + 1, state.n):
            for pair in state.pairs:
                if cooccur_only:
                    if not _both(pair, u, v):
                        continue
                elif not _mentions(pair, u, v):
                    continue
                for survivor in (u, v):
                    if rewrite_pair(pair, u, v, survivor) == pair:
                        continue
                    out.append(Partial(u, v, pair, survivor))
    return tuple(out)


def other_changes(state: State) -> tuple[Change, ...]:
    """The base changes other than a global identification."""
    return tuple(change for change in base_changes(state) if change.kind is not Kind.IDENTIFY)


def between_the_two(partial: Partial) -> bool:
    """The chosen assertion already names both terms."""
    return _both(partial.pair, partial.u, partial.v)


def obstructed(state: State, partial: Partial) -> bool:
    """Does this partial identification write some `xrx`?"""
    return not perform_partial(state, partial).legal
