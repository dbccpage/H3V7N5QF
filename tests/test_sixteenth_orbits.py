from __future__ import annotations

import pytest

from ninth.orbits import count_results as count_results_ninth
from sixteenth.explore import explore16
from sixteenth.orbits import (
    _averaged,
    count_results16,
    counts_within16,
    layer_counts16,
    ninth_part,
    one_term_round_count,
    product_count16,
    two_term_round_count16,
)
from sixteenth.state import Reading, empty16


def test_counts_match_the_exploration() -> None:
    expl = explore16(empty16(), 2, 6)
    by: dict[str, int] = {}
    for s, r in expl.depth.items():
        by[f"{s.n}/{r - s.n}"] = by.get(f"{s.n}/{r - s.n}", 0) + 1
    assert by == counts_within16(2, 6)
    assert counts_within16(2, 6)["2/4"] == 248 and counts_within16(3, 6)["3/3"] > 0
    as_set = explore16(empty16(), 2, 6, reading=Reading.SET)
    by_set: dict[str, int] = {}
    for s, r in as_set.depth.items():
        by_set[f"{s.n}/{r - s.n}"] = by_set.get(f"{s.n}/{r - s.n}", 0) + 1
    assert by_set == counts_within16(2, 6, Reading.SET)
    assert count_results16(2, 4, Reading.DROP) == count_results16(2, 4)


def test_record_free_part_is_the_ninth_count() -> None:
    for n in range(4):
        ours, theirs = ninth_part(n, 6)
        assert ours == theirs == count_results_ninth(n, 6)
    assert count_results16(0, 3) == [1, 0, 0, 0]
    assert layer_counts16(6) == [1, 1, 3, 9, 33, 126, 534]
    assert layer_counts16(4, None) == [1, 1, 3, 8, 29]


def test_closed_forms_and_the_product() -> None:
    assert [one_term_round_count(k) for k in range(7)] == [0, 1, 2, 4, 6, 9, 12]
    assert [count_results16(1, 5)[w] for w in range(6)] == [one_term_round_count(w + 1) for w in range(6)]
    assert [two_term_round_count16(k) for k in range(4)] == [1, 1, 3, 8]
    assert two_term_round_count16(6) == 260
    assert product_count16(1, 4) == count_results16(1, 4)
    assert product_count16(2, 4) == [1, 4, 22, 68, 216] and count_results16(2, 4) == [1, 4, 22, 76, 248]
    with pytest.raises(ValueError):
        one_term_round_count(-1)
    with pytest.raises(ValueError):
        two_term_round_count16(-1)
    with pytest.raises(ValueError):
        count_results16(-1, 2)
    with pytest.raises(ArithmeticError):
        _averaged([1], 2)
