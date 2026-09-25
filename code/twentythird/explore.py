"""Changes performed on states, the results formed afterwards (reading C-E).

Given by the seed
    Attempt every change, fewest additions first; 100 changes along each
    alternative, earlier changes on every alternative before later ones; a
    finite bound, the exact frontier, and what is complete within it.  The
    task: "Explore by performing changes on states, as the twenty-second's
    exploration does, and form the results afterwards."

Cited from the twenty-second derivation (`twentysecond.explore`) and re-checked
    Its exploration performs every change on every state it has reached (its
    plain states, least writings), fewest additions first, round by round,
    bounded in terms and rounds, and records the round each state is first
    reached (its size: 22:D4).  It mentions this seed's sameness nowhere, so it
    is run as it stands (no change) and its states are grouped afterwards by
    `result_key`.

Chosen here (reading C-E)
    The round of a result is the first round in which one of its states is
    reached.  The unchosen C-E′ groups the ninth's exploration of every state
    (`group_depths` on `ninth.explore`): compared in `twentythird.evidence`.

Derived (paper, D4 and D13)
    Every state of a result asserting the fewest asserts no pair in both
    relations, so it is one of the twenty-second's states, reached at the round
    of its size — the cost of the result.  So the round of a result is its
    cost, and the states of it reached in that round (`fewest_members`) are
    exactly its states asserting the fewest, up to writing; within a bound of
    `N` terms and `R` rounds every result with at most `N` terms and cost at
    most `R` is formed.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from twentysecond.explore import Exploration as PlainExploration
from twentysecond.explore import count_shortest_sequences as plain_sequences
from twentysecond.explore import explore as explore_plain
from twentysecond.explore import order

from twentythird.state import DState, Key, empty, result_key

__all__ = [
    "Grouped",
    "explore",
    "group",
    "group_depths",
    "order",
    "shortest_sequences",
]


@dataclass
class Grouped:
    """The twenty-second's exploration of states, and this seed's results formed from it."""

    plain: PlainExploration
    round_of: dict[Key, int]
    members: dict[Key, tuple[DState, ...]]

    def fewest_members(self, key: Key) -> tuple[DState, ...]:
        """The states of the result reached in its round: those asserting the fewest (up to writing)."""
        r = self.round_of[key]
        return tuple(m for m in self.members[key] if self.plain.depth[m] == r)

    def representative(self, key: Key) -> DState:
        """The result's first state reached (a state asserting the fewest; least writing first)."""
        return self.members[key][0]

    def ordered_keys(self) -> list[Key]:
        """The results in round order, then by their representative."""
        return sorted(self.round_of, key=lambda k: (self.round_of[k], order(self.representative(k))))

    @property
    def bound(self) -> int:
        """The bound on terms."""
        return self.plain.bound

    @property
    def rounds(self) -> int:
        """The bound on rounds."""
        return self.plain.rounds


def group_depths(depth: Mapping[DState, int]) -> dict[Key, int]:
    """The rounds of the results formed from states with their rounds: the least round of each result."""
    out: dict[Key, int] = {}
    for state, r in depth.items():
        k = result_key(state)
        if k not in out or r < out[k]:
            out[k] = r
    return out


def group(plain: PlainExploration) -> Grouped:
    """Form the results from the states an exploration reached."""
    lists: dict[Key, list[DState]] = {}
    for state in sorted(plain.depth, key=lambda s: (plain.depth[s], order(s))):
        lists.setdefault(result_key(state), []).append(state)
    members = {k: tuple(v) for k, v in lists.items()}
    round_of = {k: plain.depth[v[0]] for k, v in members.items()}
    return Grouped(plain=plain, round_of=round_of, members=members)


def explore(bound: int, rounds: int, keep_log: bool = False) -> Grouped:
    """The twenty-second's exploration from the empty state, then the results formed."""
    return group(explore_plain(empty(), bound, rounds, keep_log))


def shortest_sequences(grouped: Grouped) -> dict[Key, int]:
    """Shortest sequences to each result: the twenty-second's counts to its states asserting the fewest, added.

    A shortest sequence to a result ends at a state of it of size its cost,
    so at a state asserting the fewest (22:D4, `shortest_additions`).
    """
    counts = plain_sequences(grouped.plain)
    return {k: sum(counts[m] for m in grouped.fewest_members(k)) for k in grouped.round_of}
