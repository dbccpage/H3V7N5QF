"""What does not follow: the earlier statements, read on the states of a result asserting the fewest.

Cited from the ninth derivation (`ninth.follows`) and re-checked (computed
again)
    `STATEMENTS` are predicates on states.  A result here has several states
    asserting the fewest (up to writing), so a statement is read on each of
    them: it *holds* of a result when it holds of all of them, *fails* when it
    fails of all, and *depends on the state* when some satisfy it and some do
    not — a verdict the twenty-second, with one plain state per result, could
    not give.

Defined here
    Three statements about results: the result asserting nothing on its terms
    (`nothing_asserted_up_to_raising`); the result unchanged by exchanging the
    two relations (`unchanged_by_exchange_here`); one state asserting the
    fewest (`one_state_asserting_the_fewest`).
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from ninth.follows import STATEMENTS as EARLIER

from twentythird.explore import Grouped
from twentythird.state import DState, Key, is_nothing, result_key, swap

__all__ = ["EARLIER", "HERE", "Verdict", "verdicts"]


def nothing_asserted_up_to_raising(state: DState) -> bool:
    """The result is the one asserting nothing on its terms."""
    return is_nothing(state)


def unchanged_by_exchange_here(state: DState) -> bool:
    """Exchanging the two relations gives the same result here."""
    return result_key(swap(state)) == result_key(state)


#: Statements about results, true or false of all the states of one result alike.
HERE: tuple[Callable[[DState], bool], ...] = (nothing_asserted_up_to_raising, unchanged_by_exchange_here)


@dataclass(frozen=True)
class Verdict:
    """Where a statement first holds, fails, and depends on the state, among the explored results."""

    statement: str
    wording: str
    holds_at: Key | None
    fails_at: Key | None
    depends_at: Key | None
    results_where_it_depends: int

    @property
    def in_every_result(self) -> bool:
        """The statement held of every explored result."""
        return self.fails_at is None and self.depends_at is None

    @property
    def independent(self) -> bool:
        """Some explored result satisfies it and some violates it."""
        return self.holds_at is not None and self.fails_at is not None


def verdict(grouped: Grouped, statement: Callable[[DState], bool], name: str, wording: str) -> Verdict:
    """Read `statement` on every state asserting the fewest of every explored result."""
    holds: Key | None = None
    fails: Key | None = None
    depends: Key | None = None
    count = 0
    for key in grouped.ordered_keys():
        seen = {bool(statement(m)) for m in grouped.fewest_members(key)}
        if seen == {True}:
            holds = holds if holds is not None else key
        elif seen == {False}:
            fails = fails if fails is not None else key
        else:
            depends = depends if depends is not None else key
            count += 1
    return Verdict(name, wording, holds, fails, depends, count)


def one_state_asserting_the_fewest(grouped: Grouped) -> Verdict:
    """The statement "one state asserting the fewest", read on the result."""
    holds: Key | None = None
    fails: Key | None = None
    for key in grouped.ordered_keys():
        if len(grouped.fewest_members(key)) == 1:
            holds = holds if holds is not None else key
        else:
            fails = fails if fails is not None else key
    return Verdict("one_state_asserting_the_fewest", "The result has one state asserting the fewest, up to writing.",
                   holds, fails, None, 0)


def verdicts(grouped: Grouped) -> tuple[Verdict, ...]:
    """Verdicts for every statement tested: the earlier ones, then this seed's."""
    out = [verdict(grouped, s, s.__name__, (s.__doc__ or "").strip()) for s in EARLIER]
    out += [verdict(grouped, s, s.__name__, (s.__doc__ or "").strip()) for s in HERE]
    out.append(one_state_asserting_the_fewest(grouped))
    return tuple(out)
