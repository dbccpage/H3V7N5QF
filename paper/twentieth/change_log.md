# Change log

1. **Plan in `CLAUDE.md`, committed alone** with the nineteenth and
   twenty-first plans.

2. **`lean4/lakefile.toml`: library `Twentieth`.** Shared file. Recorded in
   `paper/change_log.md`.

3. **`ci/check_mutation_bite.py`: a twentieth panel** for every disagreement
   field of `OrderCheck`.

4. **The package, the library, the evidence, and this paper.** O1 matches
   the base closure. O2, capped at round 2, does not. The added count is
   not the round.

5. **Review repair.** The O2 comparison set O2 after as many expansions as O1
   has round-2 results (12 or 11) against O1's round-2 set, which O1 reaches
   after 4 expansions; the 17 and 18 results that "enter" are mostly the
   extra budget. The summary now also records O1's budget and O2 at that
   budget (`matched_leave`, `matched_enter`): the order alone moves 5 and 4,
   or 5 and 3, results. `code/twentieth/order.py` gains `changes_priority` (O1
   with the same cap) sharing one loop with `additions_priority`. O1 ("O2 run
   to exhaustion") is now computed: a new disagreement field
   `o2_closure_differs`, with a bite case, compares O2 and O1 each run until
   nothing is pending. O2 was open with the re-check "the base leaves the same
   question open"; the base does not (D12, with Lean `fewest_changes_lower_A`,
   `_B`), so it is now W11. The cited base theorems are printed in the axiom
   report.
