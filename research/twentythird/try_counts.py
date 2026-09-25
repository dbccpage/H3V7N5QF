"""Scratch: the counts against each other and against the grouped exploration (not evidence)."""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))

from twentythird.cost import cost, cost_closed, fewest_states, search_fewest, fewest  # noqa: E402
from twentythird.explore import explore  # noqa: E402
from twentythird.orbits import (  # noqa: E402
    counts_within,
    listing_counts,
    three_term_counts,
    two_term_count,
    two_term_count_by_points,
)


def main() -> None:
    for t in range(8):
        assert two_term_count(t) == two_term_count_by_points(t), t
    print("two-term closed form = listing of points")
    print("two terms listing", listing_counts(2, 6), [two_term_count(t) for t in range(7)])
    t0 = time.time()
    print("three terms", three_term_counts(5), listing_counts(3, 5), round(time.time() - t0, 1))
    for bound, rounds in ((5, 8), (3, 10), (2, 24)):
        t0 = time.time()
        g = explore(bound, rounds)
        t1 = time.time()
        got: dict[str, int] = {}
        bad = 0
        for k, r in g.round_of.items():
            rep = g.representative(k)
            c = cost(rep)
            if c != r:
                bad += 1
            key = f"{k[0]}/{r - k[0]}"
            got[key] = got.get(key, 0) + 1
            cc = cost_closed(rep)
            if cc is not None and cc != c:
                bad += 1
            if len(fewest_states(rep)) < len(g.fewest_members(k)):
                bad += 1
        t2 = time.time()
        want = counts_within(bound, rounds)
        t3 = time.time()
        print(bound, rounds, "results", len(g.round_of), "states", len(g.plain.depth), "bad", bad,
              "counts equal", got == want, "times", round(t1 - t0, 1), round(t2 - t1, 1), round(t3 - t2, 1))
        if got != want:
            for key in sorted(set(got) | set(want)):
                if got.get(key) != want.get(key):
                    print("  ", key, got.get(key), want.get(key))
    g = explore(5, 8)
    small = [g.representative(k) for k in g.round_of if k[0] <= 3]
    t0 = time.time()
    print("search agrees", all(search_fewest(s) == fewest(s) for s in small), len(small), round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
