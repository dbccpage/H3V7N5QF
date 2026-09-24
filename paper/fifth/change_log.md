# Change log, fifth derivation

Each material change, and its reason. Newest last. Commits are on the branch
the run started on (`worktree-third-derivation`, the worktree of this
repository in which the third and fourth derivations were made; the branch
was brought to `origin/main` — which had merged the fourth derivation and
installed the fifth seed — before any work of the fifth derivation).

1. **`CLAUDE.md` gained the fifth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/fifth/prompt.md`. The earlier plans above it are unchanged.

2. **The state model is the fourth derivation's, imported unchanged
   (`fourth.state`, Lean `MSt`); two operations are new: removal (one
   multiplicity falls by one) and identification (the multiplicities of the
   pairs that become one pair add up).** Reason: the seed changes the kinds
   of change, not the state. The sum reading of identification is the
   reading C5″ of the paper; the fourth's `image` (which read a build the
   same way) computes it. Lean: `MSt.identify` gives a pair of the outcome
   the sum, over the pairs of terms that become it, of their multiplicities —
   a sum over a fibre — so that the total multiplicity is kept by one lemma
   (`Finset.sum_fiberwise_of_maps_to`) and every other fact about it follows
   from "a merged multiplicity is at least each part" and "a multiplicity of
   the outcome is zero exactly when every part was".

3. **Layout: a new package `code/fifth/` importing from `code/xry/`,
   `code/second/`, `code/third/` and `code/fourth/` only what removal and
   identification leave intact; no earlier module is modified.** Reason: the
   task allows changes to the earlier derivations' files only to correct a
   defect, and none was found. Imported: the counted state and its sameness,
   the kinds of change and answer kinds, the identification map on written
   terms, the fourth's build reading and one-term builds, the size of what
   is given, the cycle machinery and the series of the orbit counts, the
   statements tested, the fewest-classes count, the writers, the Lean report
   runner, and the fourth's exploration, sequence count and reachability for
   the comparison. Defined afresh: the four kinds, obstruction, the answers,
   the exploration, the cost, reachability, the counts of shortest sequences,
   the independent count by destroyed givens, the statements new to this seed.

4. **The list of changes of a result is: identifications (each unordered
   pair of terms), removals (each asserted pair once), a term, every ordered
   pair as an addition — `C(n, 2) + d + 1 + n²` changes.** Reason: the seed's
   "fewest additions first" and the fourth's "every ordered pair, asserted
   already or not" (4:C5′); one removal lowers by one, so an assertion
   asserted `k` times has one removal change, not `k`.

5. **"Remove the obstruction" is a sequence of removals then the
   identification for an obstructed identification (`M(u,v) + M(v,u) + 1`
   changes), and is recorded as coinciding with refusal for an obstructed
   addition of `xrx`.** Reason: the first derivation's reading C7 restated for
   multiplicities; the fourth's declaration "impossible: no change lowers a
   multiplicity" no longer holds as a reason and is replaced by
   `"coincides with refusal: the obstruction is the assertion the change
   itself adds; removing it is not adding it, and nothing changes"`.

6. **The number recorded per result is the number of *shortest* sequences
   reaching it, with a flag saying whether the count is exact within the
   bound; the number of all sequences is infinite for every result.** Reason:
   the fourth's `count_sequences` relied on every change raising the round by
   one, which fails here (a removal can lower it); a dynamic programme over
   the cost-raising changes counts the shortest sequences, exact where the
   paper proves (D14: results with fewer terms than the bound or with the
   names apart; all results under FREE). The two-change cycle at every state
   (add a term, identify it back) is recorded per result.

7. **The independent count is by terms, total multiplicity *and destroyed
   givens*, with the first derivation's five kinds of named pair and the
   fourth's series per cycle.** Reason: every legal state is a result and its
   round is its cost, which depends on the destroyed givens; the completeness
   certificate must therefore restrict the count to cost within the rounds
   per kind. The fourth's counts must reappear as the `lost = 0` part, and
   `counts.csv` records both.

8. **Reachability is tested by the names criterion against a search along
   the changes among the results of a wider exploration (3 terms, the
   reachability rounds plus three), not by a breadth-first search from each
   result.** Reason: the distance between two results is no longer the
   difference of their rounds, so a search from each result would have to
   run for many rounds through states of high multiplicity; the proof of D12
   shows every sequence it uses stays within cost `max(cost) + 2` (removing a
   given unit raises the cost by one, at most twice), so a graph on the
   results within three more rounds holds a path for every reachable pair.
   The search is sound (every path is a sequence of changes) and the
   agreement with the criterion is checked on every ordered pair.

9. **The cache of least writings (`fourth.state._CANONICAL`) is emptied
   between explorations (`fifth.state.forget_canonical_forms`).** Reason:
   twelve explorations and a census in one run would otherwise keep every
   outcome ever canonicalised in memory; the cache is an optimisation and
   emptying it changes no result. This reaches into a private name of the
   fourth's module without modifying it.

10. **Lean: a fifth library `Fifth` in the same Lake package, importing
    `Fourth`; the lakefile gained the target (recorded in
    `paper/change_log.md`, item 23).** The plan's targets 1–5 and 7 closed;
    target 6 (`rename` for the four kinds, the cost in every writing, the
    every-writing statements) closed on the single attempt. Two name
    clashes with the first library (`identify_legal_iff`, `remove_legal`,
    also `size_addTerm`) are resolved by writing the namespace where the
    earlier theorem is meant; the axiom-report file writes every name in
    full for the same reason.

11. **One Lean statement was attempted and dropped: that identifying a
    build's added term back with `x` gives the would-be outcome of adding
    `xrx`, on counted states (`build_gives_back5`).** Reason: its proof by
    fibre sums hit the elaborator's heartbeat limit twice during the single
    attempt the plan allows; the statement is the fourth derivation's reading
    of a build (4:C7), checked by computation (`is_build_of`) on the
    beginnings and, on supports, by the first derivation's `build_gives_back`.
    Recorded as open (O6) rather than weakened silently. No claim of the paper
    rests on it.

12. **Re-runs of the earlier derivations' checks.** After this work
    `python code/generate_fifth.py --check` matched; the four earlier Lean
    reports (`python code/lean_report.py`, `_second`, `_third`, `_fourth`)
    were re-run and the four earlier `--check`s (`python code/generate.py
    --check`, `_second`, `_third`, `_fourth`) were re-run; their outcomes are
    recorded here at the end of the run (item 15).

13. **Slips found by the tests during the run, all in the fifth's own test
    files, none in the derivation's code.** Numbers guessed before the
    evidence existed (the FREE two-term rounds, the split by destroyed givens,
    the count totals, one cost) were corrected to the computed values; a
    witness for the fewest classes falling was wrong (removing `brc` from
    `a b; arb(2) brc` leaves two classes) and was replaced by the triangle
    `arb brc cra`; and an assertion that a change can keep the round was
    refuted by the run itself — every change moves the cost by an odd amount
    (D8(v)), which was then proved in Lean (`Reach5.size_parity`) and added
    to the paper. No evidence had been written.

14. **The mypy gate flagged two comparisons on untyped dictionary values in
    `tests/test_fifth_evidence.py`; they were rewritten as inequalities with
    zero.** No derivation code changed.

15. **Outcome of the re-runs (item 12).** `python code/lean_report.py`,
    `python code/lean_report_second.py`, `python code/lean_report_third.py`
    and `python code/lean_report_fourth.py` each built all five libraries and
    rewrote their `lean_axioms.txt` and manifest byte-identically (`git
    status` shows no change under `evidence/`, `evidence/second/`,
    `evidence/third/`, `evidence/fourth/`); `python code/generate.py --check`,
    `python code/generate_second.py --check`, `python code/generate_third.py
    --check` and `python code/generate_fourth.py --check` each reported a
    match with a fresh regeneration — the third's check, which the fourth
    derivation could not finish (4:change log 13), completed this time. So
    the evidence of all four earlier derivations still regenerates.

16. **The prose watchlist pin was regenerated for the fifth paper.** Its four
    watched terms (six hits) all lie in §10, the final section; the pin
    records them, and the gate is clean on the tracked tree. The full test
    suite was first run before the pin was refreshed and its watchlist test
    failed on exactly those hits; re-run after the pin, all tests pass.

17. **Review fixes: dropped injection tests restored, full coverage regained.**
    A review of the derivation's pull request found four differential-check
    failure branches in `code/fifth/evidence.py` that no test exercised: the
    reachability `criterion_agrees_with_search` disagreement (678) and the
    two-term binomial check (452) — for both of which the fourth derivation
    had injection tests (`test_reach_reports_a_disagreement`,
    `test_two_term_binomial_check_can_fail`) that the fifth dropped — and the
    two new cost checks in `check_changes` (366 `cost_rises_by_at_most_one`,
    368 the per-change `raises_by_one` rule), which had none. Each check is
    gated by `run_ok`/`reach_ok`, so a real defect fails the gate, but the
    detection logic itself was never proven to fire, against this repository's
    injection discipline. Added `test_reach_reports_a_disagreement`,
    `test_two_term_binomial_check_can_fail`,
    `test_check_changes_reports_cost_disagreements`, and
    `test_check_changes_counts_a_change_that_keeps_the_round` (the last for the
    benign step-zero branch at 377). Line coverage returns to 100%. No
    derivation code, evidence, claim, or claim status changed; the checks the
    tests exercise are unchanged.

## Whole-repo review repairs (2026-09-23)

- F006: printed the cited base cost bound and regenerated the Lean report and manifest. F013: filled O1/O2 evidence with the fourth seed and own series/round references. No claim or theorem statement changed.
