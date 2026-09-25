"""Print the main figures of `evidence/twentysecond/summary.json` (research helper, not evidence)."""

from __future__ import annotations

import json
from pathlib import Path

s = json.loads((Path(__file__).resolve().parents[2] / "evidence" / "twentysecond" / "summary.json").read_text(encoding="utf-8"))
print("clean:", s["every_check_clean"], {k: len(v) for k, v in s["disagreements"].items() if v})
for tag, run in s["runs"].items():
    print(tag, run["results"], run["results_by_terms"], "attempts", run["attempts"], "last new", run["last_round_with_a_new_result"])
    print("  every:", run["statements_holding_in_every_result"], "none:", run["statements_holding_in_no_result"])
    print("  sequences total", run["shortest_sequences_total"], "one", run["results_reached_by_one_shortest_sequence"])
    print("  frontier", run["frontier_states"], run["frontier_entries"], "awaiting", run["results_of_the_last_round_whose_changes_await"])
    print("  seventh", run["seventh_derivation"])
    print("  ninth", run["ninth_derivation"])
    ch = run["changes"]
    print("  changes", {k: v for k, v in ch.items() if k != "how_each_kind_moves_what_is_recorded"})
    for kind, moves in ch["how_each_kind_moves_what_is_recorded"].items():
        print("   ", kind, moves)
print("reach", s["reachability"])
print("sameness", s["generated_sameness"])
ic = s["independent_counts"]
print("totals", ic["totals_by_terms"], "within 100 rounds, two terms:", ic["results_with_at_most_two_terms_within_100_rounds"])
print("layers", ic["results_of_each_round_without_bound"])
print("given", s["given"], "full log", s["attempts_in_full_log"])
