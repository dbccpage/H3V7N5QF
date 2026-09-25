"""What does not follow: statements read on the states of a result asserting the fewest.

Cited from the ninth and twenty-third derivations (`ninth.follows`,
`twentythird.follows`) and re-checked (computed again)
    Their statements are predicates on two-relation states; here they are read
    on the base of every state of a result asserting the fewest, with the
    twenty-third's three verdicts: *holds* (on all), *fails* (on all),
    *depends on the state* (on some and not others).

Defined here
    Statements about the filled terms: some term is filled; every term is
    filled; every filled term balances; the result is told apart from the one
    asserting nothing by a filled term that does not balance; a term that does
    not balance is filled (every loop of non-zero excess is at a filled term);
    unchanged by exchanging the two relations, the filled terms kept.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from ninth.follows import STATEMENTS as NINTH
from twentythird.follows import HERE as TWENTYTHIRD

from twentyfourth.explore import Grouped
from twentyfourth.state import DState, FState, Key24, result_key, swap, told

__all__ = ["EARLIER", "HERE", "Verdict", "on_base", "verdicts"]

#: The earlier statements, predicates on the base.
EARLIER = (*NINTH, *TWENTYTHIRD)


def some_term_filled(state: FState) -> bool:
    """Some term is filled."""
    return state.filled_count > 0


def every_term_filled(state: FState) -> bool:
    """Every term is filled."""
    return state.filled_count == state.n


def every_filled_term_balances(state: FState) -> bool:
    """Every filled term balances."""
    return not told(state)


def told_apart(state: FState) -> bool:
    """A filled term that does not balance tells the result apart from the one asserting nothing."""
    return told(state)


def unbalanced_loops_filled(state: FState) -> bool:
    """Every term whose `xrx` and `xsx` are asserted unequally often is filled."""
    n = state.n
    return all(state.fills[x] for x in range(n) if state.base.r[x * n + x] != state.base.s[x * n + x])


def unchanged_by_exchange(state: FState) -> bool:
    """Exchanging the two relations, the filled terms kept, gives the same result."""
    return result_key(swap(state)) == result_key(state)


#: Statements about results with filled terms.
HERE: tuple[Callable[[FState], bool], ...] = (
    some_term_filled,
    every_term_filled,
    every_filled_term_balances,
    told_apart,
    unbalanced_loops_filled,
    unchanged_by_exchange,
)


@dataclass(frozen=True)
class Verdict:
    """Where a statement first holds, fails, and depends on the state, among the explored results."""

    statement: str
    wording: str
    holds_at: Key24 | None
    fails_at: Key24 | None
    depends_at: Key24 | None
    results_where_it_depends: int

    @property
    def in_every_result(self) -> bool:
        """The statement held of every explored result."""
        return self.fails_at is None and self.depends_at is None


def verdict(grouped: Grouped, statement: Callable[[FState], bool], name: str, wording: str) -> Verdict:
    """Read `statement` on every state asserting the fewest of every explored result."""
    holds: Key24 | None = None
    fails: Key24 | None = None
    depends: Key24 | None = None
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


def on_base(statement: Callable[[DState], bool]) -> Callable[[FState], bool]:
    """An earlier statement, read on the base of a state."""

    def read(state: FState) -> bool:
        return statement(state.base)

    return read


def verdicts(grouped: Grouped) -> tuple[Verdict, ...]:
    """Verdicts for every statement tested: the earlier ones on the base, then this seed's."""
    out = []
    for s in EARLIER:
        out.append(verdict(grouped, on_base(s), s.__name__, (s.__doc__ or "").strip()))
    for h in HERE:
        out.append(verdict(grouped, h, h.__name__, (h.__doc__ or "").strip()))
    return tuple(out)
