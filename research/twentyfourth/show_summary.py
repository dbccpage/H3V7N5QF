"""Scratch (not evidence): print the headline numbers of `evidence/twentyfourth/summary.json`."""

from __future__ import annotations

import json
from pathlib import Path

s = json.loads(Path("evidence/twentyfourth/summary.json").read_text(encoding="utf-8"))
for k, v in s["runs"].items():
    print(k, {kk: v[kk] for kk in ["states_reached", "results", "results_by_terms", "frontier_entries"]})
    print("   classes", v["results_by_how_they_stand_against_the_one_asserting_nothing"])
    print("   moves", v["changes"]["how_each_kind_moves_the_cost"], v["changes"]["changes_checked"])
    print("   23rd", v["twentythird"], v["map_back"], v["shortest_sequences"], v["respect"])
    print("   per round", v["new_results_per_round"])
print(s["reachability"])
print(s["generated_sameness"])
ic = s["independent_counts"]
print(ic["results_of_round_r_with_at_most_two_terms"][:20], ic["their_sum_over_rounds_0_to_100"])
print(ic["results_of_round_r_without_a_bound_on_terms"])
print(Path("evidence/twentyfourth/readings.json").read_text(encoding="utf-8"))
print(Path("evidence/twentyfourth/given.json").read_text(encoding="utf-8"))
