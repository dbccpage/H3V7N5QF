# Change log

1. Plan and stopping conditions recorded in `CLAUDE.md` before other work
   (the prompt requires that commit on its own).
2. Reading of the seed against the base, in `research/seventeenth/`. Not
   evidence. Two readings of an obstructed change (enter it, or not) and
   two readings of "makes some `xrx`" are kept.
3. `code/seventeenth/` computes both readings. At 3 terms and 6 rounds the
   A-replace closure matches `xry.explore` and the base cost, and no result
   asserts `xrx`. The A-perform closure does: identifying `a` with `b` is
   one change whose outcome asserts `ara`, and the base cost of that outcome
   is greater than 1. A refusal changes nothing. Remove-then-identify and
   identify-then-remove end at the same state.

4. `lean4/Seventeenth/`: `LoopFree` is the base `Legal` as a predicate;
   `Step17` drops the ban's side-conditions; M1 and M2 agree on a loop-free
   state and differ on a state that already asserts `ara`; an unobstructed
   `Step17` on a loop-free state is a base `Step` and conversely; the base
   cost is the fewest changes along those steps; identifying `a` with `b` in
   what is given is one `Step17` whose outcome asserts `ara` and whose base
   cost is not that length; remove-then-identify and identify-then-remove
   end at the same state, and the second path's intermediate asserts `ara`;
   `rename` for an injective rewriting. Not yet built: `lake` checked the
   pinned packages out again and is rebuilding them, so the exit code is not
   in hand.

cycle: wrote the Lean library (`Step17`, the embedding, the A-perform witness, answers, rename) and the lakefile target; next get `lake build` green, then the paper, the ledger, and `evidence/seventeenth/`.

5. Paper, ledger, and the evidence frontier. Both unchosen beginnings
   (`ara`, `brb`) are checked. `code/seventeenth/leanreport.py` writes the
   axiom report and has not been run: this Lake rejects `-j`, so the build
   is one process with `LEAN_NUM_THREADS=4`, still compiling dependencies.

cycle: wrote the paper, the ledger, the frontier and the report writer; pytest, the coverage gate, mypy, the prose watchlist, the three ci gates and evidence `--check` are green; next read the single lake exit and, if it is 0, write `lean_axioms.txt` and open nothing further until that file is committed.

cycle: left the one `lake build Seventeenth` running (Mathlib oleans advancing, about 1294 of 8311 at 05:19; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 1599 of 8311 at 05:36, newest `Algebra/Star/StarProjection.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 1905 of 8311 at 05:56, newest `LinearAlgebra/AffineSpace/Midpoint.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 2229 of 8311 at 06:16, newest `RingTheory/MatrixPolynomialAlgebra.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 2549 of 8311 at 06:36, newest `FieldTheory/IntermediateField/Adjoin/Algebra.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

6. `lake build Seventeenth` exited 1. The failure was in `Seventeenth/Step.lean`, not in Mathlib: `obstructedM1` matched on `Step17` with the target state fixed, and that match does not eliminate into `Prop`. The target state is now a pattern. `Classical.not_not` is an `Iff`, so `loopFree_out` uses `.mp`. `not_not` and `tauto` are gone from the identify case. `lake +leanprover/lean4:v4.33.1 -d lean4 build Seventeenth` then exited 0.

cycle: fixed the Seventeenth Lean build (EXIT=0); next write `evidence/seventeenth/lean_axioms.txt` and close O1.

7. `python code/lean_report_seventeenth.py` passed. `evidence/seventeenth/lean_axioms.txt`
   records `lake build: passed`, no `sorry` / `admit` / declared axiom, and
   `#print axioms` for every cited theorem. Each depends only on `propext`,
   `Classical.choice` and `Quot.sound`. O1 is closed (K4). O2–O5 stay open.

cycle: wrote the axiom report and closed O1; the seventeenth derivation's gates are the remaining check before the branch is finished.

8. Review of pull request 39 (2026-09-23). Entries 1–7 and the cycle notes
   above are left as written; this entry corrects them.
   - Entry 7 said the report has "`#print axioms` for every cited theorem".
     It did not: ten cited theorems had no line (`loopyWitness_hasXrx`,
     `identify_givenA_reach`, `oneLoop_hasXrx`, `add_ara_reach`, and
     `wf`, `nonempty`, `names_stay_merged` for both `Reach17` and
     `ReachAll`). They are added to `Seventeenth/Axioms.lean` and the
     report is regenerated. `tests/test_seventeenth_leanreport.py` now
     fails when a theorem of `lean4/Seventeenth/` cited in the ledger or
     the paper has no line in `lean_axioms.txt`. Proved by injection:
     with the `identify_givenA_reach` line removed from the report, the
     test failed naming that theorem; with the bytes restored, it passed.
   - The frontier listed only attempts that leave the term bound, but the
     round bound also cut the closures: every A-perform run and the
     names-kept A-replace runs still found new results in round 6. The
     frontier now also lists those 400 results as `|rounds` entries, with
     per-run counts in `unexpanded_by_run` (K2).
   - What each result adds to what is given (G11) was not recorded. It is
     now, for all 1389 results, in `results_bound3_rounds6.csv` (K5).
   - `Step17.toStep`, `Reach.toReach17` and `Reach17.toReach` took a
     loop-free hypothesis they never used. It is dropped, and D4 states the
     embedding with no hypothesis on the state.
   - D1 marks its second sentence as true by the definition of M1. D7's
     re-check now says the base theorem is cited, not re-proved. The
     paper's references to C3 and D11, which named no row of this ledger,
     now read 1:C3 and D10.
   - The `ara` half of `perform_misses_witness` named the same state as
     `loop_beginning_not_in_perform`, and is removed. `passes` and the
     summary now read the disagreement lists off the `LoopCheck` fields.
   - Two shared files changed by this derivation were not logged: the
     seventeenth panel in `ci/check_mutation_bite.py`, and the paper's
     pinned hits in `ci/prose_watchlist.json`.

## Whole-repo review repairs (2026-09-23)

- F001: printed twelve cited base theorems and regenerated the Lean report and manifest. No theorem statement changed.
