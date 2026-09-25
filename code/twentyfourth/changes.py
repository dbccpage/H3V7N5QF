"""Changes of the twenty-fourth seed: the four kinds of the twenty-third, and filling one term.

Given by the seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion; filling one term.  Nothing else is a
    change.  Identifying two terms replaces both by one term in every
    assertion.

Cited from the ninth derivation (`ninth.changes`) and re-checked (no change)
    `Change`, `Kind`, `changes` and `perform` act on the two-relation state
    and mention no filled term: the four kinds are performed on the state's
    `base` as they stand.  `identification_map` (`xry.changes`) says where each
    term goes (the one term written as the smaller); the filled terms follow
    it.

Chosen here (readings C-F1, C-I1, C-O of the paper; unchosen readings kept)
    * Filling `x` makes `x` filled and changes nothing asserted; filling a
      filled term is not a change (`FILL_MARK`).  Unchosen: `FILL_COUNT`
      (C-F2, a count raised by one), `FILL_LOOPS` (C-F3, also asserting `xrx`
      and `xsx` once), `FILL_BALANCE` (C-F4, also adding the missing `xrx` or
      `xsx` until they are asserted equally often).
    * Identifying: the one term is filled when either was (`ID_EITHER`, C-I1);
      unchosen `ID_BOTH` (C-I2) and `ID_NEVER` (C-I3).
    * The order of the attempts, fewest additions first: identifications,
      removals in `r`, in `s`, fillings (they add no term and no assertion), a
      term, additions in `r`, in `s`.
"""

from __future__ import annotations

from dataclasses import dataclass

from ninth.changes import Change, Kind, changes, perform
from xry.changes import identification_map

from twentyfourth.state import DState, FState

__all__ = [
    "Change",
    "Fill",
    "FILL_BALANCE",
    "FILL_COUNT",
    "FILL_LOOPS",
    "FILL_MARK",
    "ID_BOTH",
    "ID_EITHER",
    "ID_NEVER",
    "Kind",
    "Move",
    "Reading",
    "CHOSEN",
    "is_raising",
    "kind_of",
    "moves",
    "perform24",
    "written",
]

FILL_MARK = "mark"
FILL_COUNT = "count"
FILL_LOOPS = "loops"
FILL_BALANCE = "balance"
ID_EITHER = "either"
ID_BOTH = "both"
ID_NEVER = "never"


@dataclass(frozen=True)
class Reading:
    """What filling does, and what identifying does to filled terms."""

    fill: str = FILL_MARK
    identify: str = ID_EITHER

    def __post_init__(self) -> None:
        if self.fill not in (FILL_MARK, FILL_COUNT, FILL_LOOPS, FILL_BALANCE):
            raise ValueError("an unknown reading of filling")
        if self.identify not in (ID_EITHER, ID_BOTH, ID_NEVER):
            raise ValueError("an unknown reading of identifying")

    @property
    def tag(self) -> str:
        """A short name, for files and summaries."""
        return f"fill-{self.fill}_identify-{self.identify}"


#: The chosen reading: C-F1 and C-I1.
CHOSEN = Reading()


@dataclass(frozen=True)
class Fill:
    """Filling the term `x`."""

    x: int

    def written(self, state: FState) -> str:
        """The change in words, using the state's writing of its terms."""
        return f"fill {state.base.term_writing()[self.x]}"


Move = Change | Fill


def kind_of(change: Move) -> str:
    """The kind of a change, in words."""
    return "fill one term" if isinstance(change, Fill) else change.kind.value


def written(change: Move, state: FState) -> str:
    """The change in words."""
    return change.written(state) if isinstance(change, Fill) else change.written(state.base)


def is_raising(change: Move) -> bool:
    """Is `change` one that a shortest sequence may use: adding a term, adding an assertion, filling?"""
    return isinstance(change, Fill) or change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)


def moves(state: FState, reading: Reading = CHOSEN) -> tuple[Move, ...]:
    """Every change of `state`, fewest additions first (reading C-O)."""
    four = changes(state.base)
    first = [c for c in four if c.kind in (Kind.IDENTIFY, Kind.REMOVE)]
    rest = [c for c in four if c.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)]
    fills: list[Move] = [Fill(x) for x in range(state.n) if reading.fill == FILL_COUNT or not state.fills[x]]
    return (*first, *fills, *rest)


def _identify_fills(state: FState, x: int, y: int, reading: Reading) -> tuple[int, ...]:
    q = identification_map(state.n, x, y)
    out = [0] * (state.n - 1)
    for t, k in enumerate(state.fills):
        if t not in (x, y):
            out[q[t]] = k
    fx, fy = state.fills[x], state.fills[y]
    how = reading.identify
    if how == ID_EITHER:
        # counted fillings add up, as merged multiplicities do (9:C5⁗); a mark is kept
        out[q[x]] = fx + fy if reading.fill == FILL_COUNT else max(fx, fy)
    elif how == ID_BOTH:
        out[q[x]] = min(fx, fy)
    else:
        out[q[x]] = 0
    return tuple(out)


def _fill(state: FState, x: int, how: str) -> FState:
    n = state.n
    if not 0 <= x < n:
        raise ValueError("a filled term is a term of the state")
    if how != FILL_COUNT and state.fills[x]:
        raise ValueError("filling a filled term is not a change")
    fills = list(state.fills)
    fills[x] = fills[x] + 1 if how == FILL_COUNT else 1
    base = state.base
    if how in (FILL_LOOPS, FILL_BALANCE):
        r = list(base.r)
        s = list(base.s)
        i = x * n + x
        if how == FILL_LOOPS:
            r[i] += 1
            s[i] += 1
        else:
            top = max(r[i], s[i])
            r[i], s[i] = top, top
        base = DState(n, tuple(r), tuple(s))
    return FState(base, tuple(fills))


def perform24(state: FState, change: Move, reading: Reading = CHOSEN) -> FState:
    """The outcome of `change` under `reading`."""
    if isinstance(change, Fill):
        return _fill(state, change.x, reading.fill)
    base = perform(state.base, change)
    if change.kind is Kind.IDENTIFY:
        return FState(base, _identify_fills(state, change.x, change.y, reading))
    if change.kind is Kind.ADD_TERM:
        return FState(base, (*state.fills, 0))
    return FState(base, state.fills)
