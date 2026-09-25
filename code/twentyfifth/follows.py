"""What does not follow: the earlier statements and this seed's, read on the states of a result.

Cited from the twenty-third derivation (`twentythird.follows`) and re-checked
(computed again)
    Its statements (`EARLIER`: the ninth's, about the assertions of a state;
    `HERE`: the result asserting nothing, unchanged by the exchange) are read on
    every state of a result asserting the fewest, with three verdicts: holds on
    all, fails on all, depends on the state.  The filled triples do not touch
    them.

Defined here
    Statements about the filled triples: some triple filled; every filled
    triple balances (not told); blind (no filling could tell the result);
    the exchange keeps the result (its assertions exchanged, its filled triples
    kept).  Each is the same on every state of a result.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from twentythird.follows import EARLIER
from twentythird.follows import HERE as HERE23

from twentythird.state import DState

from twentyfifth.explore import Grouped
from twentyfifth.state import FState, Mark, result_mark, swap25
from twentyfifth.told import blind, told

__all__ = ["FILLED", "Verdict", "on_state", "verdicts"]


def some_triple_filled(fs: FState) -> bool:
    """Some three terms are filled."""
    return bool(fs.filled)


def every_filled_triple_balances(fs: FState) -> bool:
    """Every filled triple balances: filled triples that do not balance do not tell the result from nothing."""
    return not told(fs)


def no_filling_tells_it(fs: FState) -> bool:
    """Every sum around three different terms is zero both ways round: no filling could tell the result."""
    return blind(fs.state)


def unchanged_by_exchange_with_fillings(fs: FState) -> bool:
    """Exchanging the two relations, the filled triples kept, gives the same result."""
    return result_mark(swap25(fs)) == result_mark(fs)


#: Statements about the filled triples, the same on every state of a result.
FILLED: tuple[Callable[[FState], bool], ...] = (
    some_triple_filled,
    every_filled_triple_balances,
    no_filling_tells_it,
    unchanged_by_exchange_with_fillings,
)


@dataclass(frozen=True)
class Verdict:
    """Where a statement first holds, fails, and depends on the state, among the explored results."""

    statement: str
    wording: str
    holds_at: Mark | None
    fails_at: Mark | None
    depends_at: Mark | None
    results_where_it_depends: int

    @property
    def in_every_result(self) -> bool:
        """The statement held of every explored result."""
        return self.fails_at is None and self.depends_at is None

    @property
    def independent(self) -> bool:
        """Some explored result satisfies it and some violates it."""
        return self.holds_at is not None and self.fails_at is not None


def verdict(grouped: Grouped, statement: Callable[[FState], bool], name: str, wording: str) -> Verdict:
    """Read `statement` on every state asserting the fewest of every explored result."""
    holds: Mark | None = None
    fails: Mark | None = None
    depends: Mark | None = None
    count = 0
    for mark in grouped.ordered_marks():
        seen = {bool(statement(m)) for m in grouped.fewest_members(mark)}
        if seen == {True}:
            holds = holds if holds is not None else mark
        elif seen == {False}:
            fails = fails if fails is not None else mark
        else:
            depends = depends if depends is not None else mark
            count += 1
    return Verdict(name, wording, holds, fails, depends, count)


def on_state(statement: Callable[[DState], bool]) -> Callable[[FState], bool]:
    """A statement about the assertions, read on a state with filled triples."""

    def read(fs: FState) -> bool:
        return statement(fs.state)

    return read


def verdicts(grouped: Grouped) -> tuple[Verdict, ...]:
    """Verdicts for every statement tested: the earlier ones on the assertions, then this seed's."""
    out = [verdict(grouped, on_state(s), s.__name__, (s.__doc__ or "").strip()) for s in (*EARLIER, *HERE23)]
    out += [verdict(grouped, f, f.__name__, (f.__doc__ or "").strip()) for f in FILLED]
    return tuple(out)
