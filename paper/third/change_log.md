# Change log, third derivation

Each material change, and its reason. Newest last. Commits are on the branch
the run started on (`worktree-third-derivation`, a worktree of this
repository).

1. **`CLAUDE.md` gained the third derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/third/prompt.md`. The earlier plans above it are unchanged.

2. **The worktree had no `lean4/.lake`; a local junction
   `lean4/.lake/packages` to the main checkout's `lean4/.lake/packages` was
   made.** Reason: the pinned dependencies are already in this repository's
   main checkout at exactly the revisions of the committed manifest (checked
   revision by revision before Phase 0), so no download was needed and none
   happened; the build directory `lean4/.lake/build` is the worktree's own.
   `.lake/` is ignored by git and nothing of it is committed.

3. **Layout: a new package `code/third/` that imports from `code/xry/` and
   `code/second/`; no first- or second-derivation module is modified.**
   Reason: the task allows changes to the earlier derivations' files only to
   correct defects, and none was found. What is reused is imported: states,
   sameness, the attempt records, the writers (first derivation); the cost in
   closed form, the counts of results, the statements tested, the fewest
   classes, the plan, the FREE cost check, the exploration with
   identifications left out (second derivation). What the seed changes is
   defined afresh: the list of changes, the answers, the exploration,
   reachability by containment, the counts that never decrease, the number
   of sequences per result. `third.changes.changes` builds the list directly
   and a test checks it equals the second derivation's list without its
   identifications; `third.changes.perform` refuses a removal and an
   identification.

4. **Every obstructed attempt records "remove the obstruction: impossible:
   the obstruction is the assertion the change itself adds; no change
   un-asserts it, and not adding it is refusal".** Reason: the seed asks to
   declare and record the answer; under this seed the only obstructed change
   is adding `xrx`, whose obstruction is its own assertion, and the record
   says which reading is impossible and which coincides with refusal (C7).

5. **The second derivation's exploration without identifications is run
   beside the third exploration in every run and both census runs, and the
   two are compared result by result, round by round, attempt by attempt.**
   Reason: rule 5 of the task — the second derivation's computed statement
   "additions alone reach the same results in the same rounds" is the
   statement this seed's exploration must agree with, and the comparison is
   its computed re-check.

6. **Reachability is tested by an embedding (a one-to-one carrying map) and,
   on every pair, also by the second derivation's carrying map; the pairs the
   second reaches and the third does not are counted, and the check requires
   that no pair is reachable here and not there and that no two different
   results reach each other.** Reason: D12 and D13 claim exactly these, and
   the second derivation's reachability files are the natural comparison.

7. **A per-result count of the sequences of changes reaching it, and the
   check that every change within the bound raises the round by one.**
   Reason: D8 claims that every sequence has the same length; the round check
   is its computed form on every edge within the bound, and the sequence count
   is exact within the bound (D14 (iv)) and gives the witnesses of N9.

8. **Lean: a third library `Third` in the same Lake package; the third seed's
   changes are a new inductive `Step2` with embeddings into the second's
   `Step3` and, through it, the first's `Step`.** Reason: the embedding is the
   formal form of the task's rule 5. The lakefile of the first derivation
   gained the library target and a default target; that edit is recorded in
   `paper/change_log.md` (item 21).

9. **All five Lean targets of the plan closed**, including target 5
   (`Step2.rename`, `Reach2.rename`, the every-writing statements) and both
   directions of the reachability criterion (`reach2_iff`,
   `reach2_iff_some_writing`), which the second derivation had left open in
   one direction (2:O3). One name clash was repaired during the build: a
   theorem named `Reach2.antisymm_writing` made `rename` resolve to
   `Reach2.rename` inside its own statement; it is named
   `reach2_antisymm_writing`. No statement changed.

10. **A test expectation written during the run was wrong and was corrected.**
    It expected one particular embedding of a three-term state into another
    where several exist; the test now checks that the embedding found is one.
    No claim changed.

11. **`third.explore.performed` leaves out results first reached in the last
    round of a truncated run.** Found by a test with fewer rounds than the
    bound needs: such a result's changes were never attempted, so its
    outcomes are not results and the sequence count and the edge checks
    looked them up in vain. With 100 rounds nothing is left out; no evidence
    changed.

12. **Bounds kept equal to the second derivation's (FREE 5, ANCHORED 4 with
    a census at 5).** Reason: file-by-file comparability with
    `evidence/second/`; the whole generation, comparisons included, takes
    about four and a half minutes here.

13. **The prose watchlist baseline was re-pinned for `paper/third/paper.md`.**
    Reason: its final section names the nearest known results, as the task
    requires, and the census pins every such hit per file; every pinned hit
    of the third paper is in that section (checked by line number in the
    audit).

14. **Review fixes after the first complete draft (one review pass).** (a)
    The alternative "an obstructed change and its answer counted as one" had
    been said to leave the rounds unchanged (C6, D8, §7); it does not — a
    build's two additions would count as one, so `a b c; arb arc` would be
    met in round 1 — and the paper now says, as the second paper did, that it
    changes rounds but not results. D8's uniqueness of length is about
    sequences of changes, each addition counting one, and is unaffected. (b)
    The persistence of the terms, assertions and names themselves (D6) had
    been labelled as inherited from 2:D6 by embedding; it is new (from D5),
    and the second seed kept only images. (c) The ledger's D13 had said 2:N10
    "left antisymmetry open"; 2:N10 refuted it with witnesses. (d) Wording:
    §7's list of first-derivation results that fail is exactly 2:§7's; N5's
    re-check is "no change" with witnesses computed again; two informal Lean
    names in the ledger's D8 written in full; the K-claims are now cited by
    ID in §6. (e) The totals 393 and 66 cited to a test are now asserted by
    it. No number, claim status or evidence file changed.

15. **Review fixes from a code review of this branch (PR #9).** (a) The
    one-way-reachability counter in `code/third/evidence.py` (`mutual`, the
    source of `unordered_pairs_reachable_both_ways`) had no injection test,
    unlike every sibling counter in `write_reach`/`write_run`: the line that
    increments it is dead, since antisymmetry (`Reach2.antisymm`) makes a
    reverse reachability impossible, so a regression that made the column
    vacuous would pass. Added `tests/test_third_evidence.py::
    test_mutual_reachability_would_be_counted`, which monkeypatches
    `reachable` to force a reverse and asserts the counter and the gate fire;
    it also covers the previously dead line, so line coverage returns to
    100.00 % and branch to 99.13 % (K10: 263 → 264 tests). No derivation code
    changed. (b) §0 said "everything claimed as derived is in Lean"; the
    within-bound completeness (D14) and the FREE-reading characterizations
    (D8, D9) are proved in the paper and checked by computation, as bookkeeping
    rule 3 allows and the ledger already marked ("paper §4"). §0 now says so.
    No claim status or evidence file changed.

## Whole-repo review repairs (2026-09-23)

- F004: printed the cited second size bound in Third/Axioms.lean and regenerated the Lean report and manifest. No theorem statement changed.
