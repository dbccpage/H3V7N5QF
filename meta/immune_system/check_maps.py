"""Finite probes of the state-map squares and a reachability adjunction.

The universe is all states with 0, 1, or 2 terms and binary multiplicities.
The checks are computations, not general theorems. No seed or derivation file
is modified. The JSON output is stable and records counterexamples if found.
"""

from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "code"))

from eighth.state import DState, of_r  # noqa: E402
from ninth.reach import reachable as reachable9  # noqa: E402
from ninth.state import forget_names as forget9, name_terms  # noqa: E402
from seventh.reach import reachable as reachable7  # noqa: E402
from seventh.state import forget_names as forget7  # noqa: E402
from seventh.state import MState  # noqa: E402


def one_relation(n: int) -> list[MState]:
    return [MState(n, bits, None) for bits in itertools.product((0, 1), repeat=n * n)]


def two_relations(n: int) -> list[DState]:
    bits = list(itertools.product((0, 1), repeat=n * n))
    return [DState(n, r, s, None) for r in bits for s in bits]


def check() -> dict[str, object]:
    square_6_9_checked = square_8_7_checked = square_9_7_checked = adjunction_checked = 0
    square_6_9_errors: list[str] = []
    square_8_7_errors: list[str] = []
    square_9_7_errors: list[str] = []
    adjunction_errors: list[str] = []
    seventh = [s for n in range(3) for s in one_relation(n)]
    ninth = [s for n in range(3) for s in two_relations(n)]

    # Sixth -> Eighth -> Ninth versus Sixth -> Seventh -> Ninth.
    for n in (1, 2):
        for s in one_relation(n):
            for a, b in itertools.product(range(n), repeat=2):
                named = MState(n, s.mult, (a, b))
                left = forget9(of_r(named))
                right = of_r(forget7(named))
                square_6_9_checked += 1
                if left != right:
                    square_6_9_errors.append(f"{named.key()}: {left.key()} != {right.key()}")

    # Eighth -> Sixth -> Seventh versus Eighth -> Ninth -> Seventh.
    for n in (1, 2):
        for s in two_relations(n):
            for a, b in itertools.product(range(n), repeat=2):
                named = DState(n, s.r, s.s, (a, b))
                left = forget7(named.r_part())
                right = forget9(named).r_part()
                square_8_7_checked += 1
                if left != right:
                    square_8_7_errors.append(f"{named.key()}: {left.key()} != {right.key()}")

    # Ninth -> Eighth (name a term) -> Sixth -> Seventh versus Ninth -> Seventh.
    for s in ninth:
        for c in range(s.n):
            left = forget7(name_terms(s, c).r_part())
            right = s.r_part()
            square_9_7_checked += 1
            if left != right:
                square_9_7_errors.append(f"{s.key()}: {left.key()} != {right.key()}")

    # ofR ⊣ proj_r in the ungraded reachability preorder, on this universe.
    for s in seventh:
        for t in ninth:
            left = reachable9(of_r(s), t)
            right = reachable7(s, t.r_part())
            adjunction_checked += 1
            if left != right:
                adjunction_errors.append(f"{s.key()} <= {t.key()}: {left} != {right}")

    before = DState.of(1, ())
    after = DState.of(1, (), ((0, 0),))
    assert before.r_part() == after.r_part() and before != after
    assert not (square_6_9_errors or square_8_7_errors or square_9_7_errors or adjunction_errors)
    return {
        "universe": "all 0-2-term states with binary multiplicities; named square uses every name placement",
        "one_relation_states": len(seventh),
        "two_relation_states": len(ninth),
        "sixth_to_ninth_square": {"checked": square_6_9_checked, "disagreements": square_6_9_errors},
        "eighth_to_seventh_square": {"checked": square_8_7_checked, "disagreements": square_8_7_errors},
        "ninth_to_seventh_square": {"checked": square_9_7_checked, "disagreements": square_9_7_errors},
        "ofR_proj_reachability_adjunction": {"checked": adjunction_checked, "disagreements": adjunction_errors},
        "projection_stutters_on_s_addition": {"before": before.key(), "after": after.key(), "r_part": before.r_part().key()},
    }


def main() -> None:
    data = check()
    out = Path(__file__).with_name("map_checks.json")
    out.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
