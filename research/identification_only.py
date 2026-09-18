"""Side question, not cited as evidence: what do identifications alone reach?

Run from the repository root: `python research/identification_only.py`.

For every legal state with at most 4 terms (FREE sameness) follow only
unobstructed identifications until none is left.  Compare the fewest and the
most terms of such an end state with two numbers computed independently from
the state: the fewest classes into which the terms can be split so that no
class holds two related terms, and the most classes of such a split in which
any two classes hold related terms.
"""

from __future__ import annotations

import sys
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "code"))

from xry.changes import Kind, changes, obstruction, perform  # noqa: E402
from xry.explore import explore  # noqa: E402
from xry.state import Sameness, State, canonical, given  # noqa: E402


def end_states(state: State) -> set[State]:
    """States reached by unobstructed identifications alone, with none left."""
    seen = {canonical(state)}
    stack = [canonical(state)]
    ends = set()
    while stack:
        s = stack.pop()
        free = [
            c for c in changes(s) if c.kind is Kind.IDENTIFY and not obstruction(s, c)
        ]
        if not free:
            ends.add(s)
        for c in free:
            t = canonical(perform(s, c))
            if t not in seen:
                seen.add(t)
                stack.append(t)
    return ends


def splits(state: State) -> tuple[int, int]:
    """(fewest classes, most classes of a split whose classes are pairwise related)."""
    n = state.n
    fewest, most = n, 1
    for colours in product(range(n), repeat=n):
        used = sorted(set(colours))
        if used != list(range(len(used))):
            continue
        if any(colours[x] == colours[y] for x, y in state.pairs):
            continue
        k = len(used)
        fewest = min(fewest, k)
        complete = all(
            any(
                state.related(x, y)
                for x in range(n)
                for y in range(n)
                if colours[x] == i and colours[y] == j
            )
            for i in range(k)
            for j in range(i + 1, k)
        )
        if complete:
            most = max(most, k)
    return fewest, most


def main() -> None:
    expl = explore(given(False, Sameness.FREE), bound=4)
    agree = 0
    for state in expl.depth:
        ends = end_states(state)
        got = (min(e.n for e in ends), max(e.n for e in ends))
        if got != splits(state):
            print("differs:", state.written(), got, splits(state))
        else:
            agree += 1
    print(f"{agree} of {len(expl.depth)} states agree")


if __name__ == "__main__":
    main()
