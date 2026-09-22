# Change log, thirteenth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-thirteenth-derivation`.

1. **`CLAUDE.md` gained the thirteenth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/thirteenth/prompt.md`. The earlier plans above it are unchanged.

2. **Lean: a thirteenth library `Thirteenth` in the same Lake package, importing
   `Twelfth`; the lakefile gained the target (recorded in
   `paper/change_log.md`).** Targets 1–4 closed: the coarser writing is the
   sum of the two relations; it determines the finer one when nothing is
   asserted and fails on `0 r 1`; adding in `r` and adding in `s` land on
   the same coarser writing; the size descends; the ninth's
   cost/reach/results through the identity; the exchange keeps the coarser
   writing (`coarse_swap`) and carries changes (`Step13.swap`); the coarser
   witnesses that C-C2 is not the ninth's count. O2 (preimages up to
   rewriting) is paper plus computation.

3. **Layout: a new package `code/thirteenth/` importing from the earlier
   packages only what the coarser writing leaves intact; no earlier
   module is modified.** Defined afresh: coarser writings, whether they
   determine the finer one, same coarser result, the comparison with the
   ninth, the unchosen coarser exploration.

4. **Bounds lowered relative to the ninth's 5-term run.** Reason: under
   C-C1 the results are the ninth's, already certified at 5 terms with 8
   rounds; coarser classification is checked on every result within
   3 terms and 6 rounds (and 2 terms and 8). The coarser reading is at 2
   terms and 5 rounds. Declared in `Plan` and in the paper (C8′).

5. **Watchlist pin for the thirteenth paper's final section.** The census
   gained `paper/thirteenth/paper.md` (hits of graph-theory terms in §10).
   Reason: the gate tracks every watched hit; the body of the paper has
   none.

6. **Review repairs (pull request #29).** Each item corrects a defect found
   at review; the committed swap-collapse counts move (see below).
   - *The "swap collapses" count treated differing written tuples as
     different results.* `invariants.py` `swap_collapses` and
     `follows.py` `swap_same_coarse` tested `state.r != state.s` for "the
     exchange is a different finer result". A state and its exchange can have
     differing `r` and `s` tuples yet be the same result up to renaming the
     terms (for example `2::1-1*1|0-0*1`, whose exchange renames to itself).
     Both now test `not same(state, swap(state))`. The committed
     `swap_collapses` fall accordingly: 1532→1516 at 2/8, 130→124 at 3/5,
     502→492 at 3/6 (8 at 2/3 unchanged); the CSV column and `coarse_verdicts`
     follow. A regression test pins that a self-symmetric state is excluded.
   - *Claims narrowed to their evidence.* D10 is an identity (the C-C1
     exploration wraps the ninth's), so only the independent count is a
     check. K2 is attributed to the committed 2-term 8-round run, not a
     2-term 4-round run the evidence does not contain.

7. **Definitional-citation gate (`ci/check_definitional_citations.py`).** The
   new OEWAS gate flagged D6 ("the coarser writing is not a third
   multiplicity") as marked *derived* on `no_third_rel`/`coarse_not_assertion`,
   which are `rfl` on the projections and never name the coarser writing. D6
   is now marked chosen by construction (the state is `NDSt`, no coarse
   field); the Lean is definitional, not a proof of it.
