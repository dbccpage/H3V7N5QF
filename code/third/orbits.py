"""Counting the results of the third seed without listing them.

Computed.  The results within a bound are the legal states with at most that
many terms that contain what is given — the same set as under the second seed
(a theorem of the paper, proved again from the third seed: `result2_iff_A`,
`result2_iff_B`).  So their number by terms and assertions, and the number of
results of each round without any bound, are the second derivation's.

Cited from the second derivation (`second.orbits`) and re-checked
    `count_results` and `layer_counts` count states up to sameness by the
    orbit method; they mention no change.  `layer_counts` uses that the round
    of a result is its size minus the size of what is given, which holds
    again (`Reach2.length_unique`, `fewest_changes2_A`, `fewest_changes2_B`).
"""

from __future__ import annotations

from second.orbits import count_results, layer_counts

__all__ = ["count_results", "layer_counts"]
