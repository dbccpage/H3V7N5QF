# Change log, sixth derivation

Each material change, and its reason. Newest last. Commits are on the branch
the run started on (`worktree-third-derivation`, the worktree of this
repository in which the third, fourth and fifth derivations were made; the
branch was brought to `origin/main` — which had merged the fifth derivation,
installed the sixth seed, and tightened the coverage gate to require every
evidence module fully covered — before any work of the sixth derivation).

1. **`CLAUDE.md` gained the sixth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/sixth/prompt.md`. The earlier plans above it are unchanged.

2. **The state model is the fourth and fifth derivations' `MState` (Lean
   `MSt`), imported unchanged; `remove` and `identify` are the fifth's,
   imported unchanged.** Reason: the seed drops sentences and adds none; a
   state asserting some `xrx` was always representable (the earlier
   derivations kept it as the would-be outcome of an obstructed change), so
   nothing about the state or its operations changes — only which states are
   results. "Legal" (no `xrx` asserted) is kept as a property a state may
   have, tested like any other statement, no longer a condition.

3. **Layout: a new package `code/sixth/` importing from the five earlier
   packages only what legality leaves intact; no earlier module is
   modified.** Reason: the task allows changes to the earlier derivations'
   files only to correct a defect, and none was found in a file the sixth
   derivation uses as it stands. Imported: the counted state and its
   sameness, the change record, the list of changes and `perform` (the fifth
   listed every change, `xrx` included, and refused afterwards), `remove`,
   `identify`, the two-change cycle, the identification map, the size of what
   is given, `contains_given`, the cycle machinery and the series of the orbit
   counts, the statements tested, the fewest-classes count (on states
   asserting no `xrx`), the writers, the Lean report runner, and the fifth's
   exploration, sequence counts, cost, destroyed givens, counts and
   reachability for the comparison. Defined afresh: the attempt record (no
   obstruction, no answers; whether the outcome asserts some `xrx`), the
   exploration, the cost with the new destroyed givens, the rule for which
   changes raise the cost by one, the reachability criterion without legality,
   the exactness rule for the shortest-sequence counts under FREE, the
   independent count with the diagonal pairs, the two-term closed forms, and
   `has_two_way` (see item 5).

4. **The list of changes of a result is the fifth's: identifications (each
   unordered pair), removals (each asserted pair once, diagonal pairs
   included), a term, every ordered pair as an addition — `C(n, 2) + d + 1 +
   n²` changes, every one performed.** Reason: the seed's four kinds with
   nothing forbidden; "fewest additions first" orders them as before.

5. **`has_two_way` is written again for pairs of two terms; the fourth's is
   not imported.** Reason: the fourth's `has_two_way` takes a pair `(x, y)`
   with `(y, x)` asserted as "asserted both ways", which counts a diagonal
   pair `(x, x)` once `xrx` is allowed. Found by the smoke test of the
   evidence writer: the FREE closed form for the destroyed givens with `bra`
   given disagreed with the best placement on `c d; drd`. Not a defect of the
   fourth's file (under its seed no diagonal pair is ever asserted), so the
   file is unchanged; the sixth's `cost.py` records why the function does not
   survive.

6. **The destroyed givens of a state with the names one term are
   `m0 + 1 − min(M(c,c), m0)`, not the fifth's `m0 + 1`.** Reason: identifying
   `a` and `b` in what is given is now one change (outcome `a (a and b one
   term); ara`), while the fifth's potential rises by three on it; its lower
   bound used that nothing is asserted between the merged terms. With the new
   count the potential rises by at most one per change (Lean
   `Step6.costA_le`, `_B`; the identification case rests on the outcome
   asserting `crc` at least `M(a,b) + M(b,a)` times, `identify_M_ge_pair`) and
   is attained (`fewest_changes6_A`, `_B`). Checked by brute force before the
   code was written (`research/sixth/reading_the_seed.md`), then on every
   explored result in every run (`round_equals_cost_formula_for_every_result`).

7. **The comparison with the fifth's shortest-sequence counts is split: equal
   on the fifth's results with the names apart (FREE: with two or more
   terms), and strictly more on the others.** Reason: to a result with the
   names one term there is now the further shortest sequence "identify first,
   then remove `ara`"; to one with the names apart no shortest sequence
   passes through an `xrx` (adding one is cost-raising, removing it is not).
   Both halves are checked on every run (`same_shortest_sequence_counts_on_
   fifth_results_with_names_apart`, `fifth_results_with_more_shortest_
   sequences = fifth_results_with_the_names_one_term`, `…_fewer… = 0`).

8. **The exactness rule for the shortest-sequence counts under FREE gains a
   clause: exact when the result has fewer terms than the bound or no optimal
   placement of the names puts them on one term (`merged_optimal`).** Reason:
   with `xrx` allowed a merged placement can be optimal for a state with two
   or more terms (`c d; crc`, both placements destroy one given), and then a
   shortest sequence may add a term before the merge and pass through one
   more term than the result. Under the fifth seed the apart placement was
   always strictly better on such states.

9. **The independent count treats the diagonal pairs as cycles of the
   rewriting (one cycle of length `p` per cycle of the rewriting of length
   `p`), with an optional cap on the `xrx` multiplicities; the names-one-term
   kind is split by how often `crc` is asserted at the named term (not at
   all, once, twice or more); the FREE count by destroyed givens uses the
   series for "nothing off-diagonal", "no pair both ways" and "every `xrx`
   below `m`".** Reason: the cost of a result depends on these; the
   certificate compares the exploration with the count by (terms, total,
   destroyed givens). With the cap at zero the count is the fifth's, which
   `counts.csv` records and checks (`fifth_counts_are_the_xrx_free_part`).

10. **Bounds lowered twice for size, not time.** The plan's targets (4 terms
    FREE and 3 terms ANCHORED with 6 rounds; 40 two-term rounds) were raised
    after timing — the explorer runs at about 100 000 attempts per second, so
    5 terms (FREE) and 4 terms (ANCHORED) with 8 rounds, 3 terms with 10
    rounds, 2 terms with 30 rounds and an ANCHORED census at 5 terms all
    complete in about twenty minutes — but the evidence then weighed 112 MB
    (the two-term runs at 30 rounds and the 3-term runs at 10 rounds hold up
    to 100 000 results each). The two-term runs were cut to 20 rounds and
    the 3-term runs to 9 (about 50 MB); the main runs, the census and the
    reachability bounds are as timed. The seed's 100 rounds with two terms
    would hold about four million results (the round counts are cubic, D17)
    and are not run; the closed form is proved for every round.

11. **Lean: a sixth library `Sixth` in the same Lake package, importing
    `Fifth`; the lakefile gained the target (recorded in
    `paper/change_log.md`, item 24).** The plan's targets 1–5 all closed on
    the first attempt, target 5 (rewriting, the every-writing statements)
    included. Two first-library names (`size_remove`, `size_identify`) clash
    with the fifth's and are written with the namespace where the fifth's is
    meant; the axiom-report file writes every name in full for the same
    reason. Reused through the embedding `Step5.toStep6` / `Reach5.toReach6`:
    the fifth's removal paths from what is given, the moves of the names,
    the two-change cycle, the refutations of one-way reachability, and the
    rewriting lemmas for the two new kinds. Written afresh without legality:
    the addition path (`reach6_by_additions`), the potential, the criterion's
    sufficiency.

12. **Slips found by the tests during the run, all in the sixth's own test
    files, none in the derivation's code.** Numbers guessed before the
    evidence existed (a change count on `a b; arb ara`, the FREE two-term
    rounds, two orbit literals, the number of shortest sequences to the
    one-term state with `bra` given — five, not four: two orders of the two
    removals then identify, two of remove one / identify / remove `ara`, and
    identify then remove `ara` twice) were corrected to the computed values;
    a comparison with a zero-term state carried no names and raised. No
    evidence had been written.

13. **Re-runs of the earlier derivations' checks.** After this work the five
    earlier `--check`s (`python code/generate.py --check`, `_second`,
    `_third`, `_fourth`, `_fifth`) and the five earlier Lean reports were
    re-run; their outcomes are recorded at the end of the run (item 15).

14. **Review pass over paper and ledger after the first draft.** One
    sentence of D8(iv) (how the cost moves on the identification of `a` with
    `b`) was rewritten for clarity; the numbers of the runs whose rounds were
    lowered (item 10), the theorem count of the axiom report (175) and the
    test totals were filled in from the final evidence. No claim or status
    changed.

15. **Outcome of the re-runs (item 13).** `python code/generate.py --check`,
    `python code/generate_second.py --check`, `python code/generate_third.py
    --check`, `python code/generate_fourth.py --check` and `python
    code/generate_fifth.py --check` each reported a match with a fresh
    regeneration (67, 271, 319, 177 and 458 seconds here); `python
    code/lean_report.py`, `_second`, `_third`, `_fourth` and `_fifth` each
    built all six libraries and rewrote their `lean_axioms.txt` and manifest
    byte-identically (`git status` shows no change under `evidence/`,
    `evidence/second/`, `evidence/third/`, `evidence/fourth/` or
    `evidence/fifth/`). So the evidence of all five earlier derivations still
    regenerates. The sixth's own `python code/generate_sixth.py --check`
    matched (834 seconds), after `python code/generate_sixth.py` (957
    seconds) and `python code/lean_report_sixth.py`.

16. **Review fix: cover the capped branch of `orbits._at_least`.** A review of
    the pull request found the one uncovered branch in the sixth's code:
    `_at_least`'s capped inner loop (`orbits.py:192-193`) runs only when
    `cap >= 2`, but its sole caller `count_named` is invoked only with
    `cap` in {None, 0}, and the brute-force cross-check
    `test_counts_agree_with_listing` iterated only `cap in (None, 0, 1)`. The
    capped path was therefore correct but unexercised, leaving the sixth below
    the prior derivations' full coverage. Extended the cross-check to
    `cap in (None, 0, 1, 2)`, which drives the branch and validates the capped
    "k or more" arithmetic against enumeration. Line/branch coverage of
    `orbits.py` returns to 100%; no derivation code, evidence, claim, or claim
    status changed.

## Whole-repo review repairs (2026-09-23)

- F007: printed the cited Fifth containment witness and own identification theorem, then regenerated the Lean report and manifest. F013: filled O1/O2 evidence with the fourth seed and own series/round references. No claim or theorem statement changed.
