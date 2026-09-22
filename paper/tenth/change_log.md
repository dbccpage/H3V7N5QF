# Change log, tenth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-tenth-derivation`.

1. **`CLAUDE.md` gained the tenth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/tenth/prompt.md`. The earlier plans above it are unchanged.

2. **Lean: a tenth library `Tenth` in the same Lake package, importing
   `Ninth`; the lakefile gained the target (recorded in
   `paper/change_log.md`).** Targets 1–3 closed; target 4 (every-writing /
   leftover under exchange for identifications) was attempted once and
   closed for additions and removals (`leftover_swap_addTerm`,
   `leftover_swap_remove`), with the identification identity marked not in
   Lean (O2). D8 (uncleared identification) is paper plus computation (O1):
   dependent elimination on `Step9` against that pair of states did not
   close. Written: `LeftOver`, `leftoverOf`, `Tagged`, `Step10` as `Step9`,
   clearing of a removal, restorability of identifying two empty terms, the
   ninth's cost/reach/results through the identity, the tagged witnesses
   that C-L2 is not the ninth.

3. **Layout: a new package `code/tenth/` importing from the earlier
   packages only what leftover leaves intact; no earlier module is
   modified.** Defined afresh: leftover outcomes, the attempt record, the
   comparison with the ninth, the unchosen tagged exploration.

4. **Bounds lowered relative to the ninth's 5-term run.** Reason: under
   C-L1 the results are the ninth's, already certified at 5 terms with 8
   rounds; leftover classification is checked on every performed change
   within 3 terms and 6 rounds (and 2 terms and 8). The tagged reading is
   at 2 terms and 4 rounds. Declared in `Plan` and in the paper (C8′).

5. **Review repairs (pull request #26).** Each item corrects a defect found
   at review; no computed number moved.
   - *Lean and Python read "restores" differently.* `leftoverOf` asked for
     `Step9 t s` exactly, while `restores_in_one` compares up to writing
     (`same`). They disagreed: with a loop on term 1 of two terms,
     identifying 0 and 1 was clearable in Python and uncleared in Lean
     (identifying in the other order was clearable in both), so the Lean
     outcome depended on which term the identification kept. `leftoverOf`
     now asks for some `Step9 t (rename9 π s)`, the seed's "differ only in
     how their terms are written"; `rename9_refl` gives the witness for
     `leftover_identify_twoEmpty`.
   - *The identification check restated its definition.* `check_leftovers`
     compared `leftover_of` with the same `restores_in_one` test it is made
     of, so it could not disagree. It now compares it with an independent
     criterion computed from the start alone (`bare_criterion`: clearable iff
     one of the two terms is bare), proved in the paper (D8, which it
     generalizes from the one witness it had) and checked on every
     identification of every run. A test drives it with a flipped outcome.
   - *Two injection tests never called the code under test.* In
     `test_compare_with_ninth_notices` the shifted-round and lost-result
     cases changed the exploration and then asserted only their own change.
     They now call `compare_with_ninth` and assert the round disagreement,
     the missing result and the failed independent count.
   - *Claims narrowed to their evidence.* D10: the comparison with the ninth
     is an identity (the C-L1 exploration wraps the ninth's), so only the
     independent count is a check. D6: by construction of C-L1;
     `no_third_rel` and `leftover_not_assertion` are definitional and no
     longer cited as its proof. D12: `tagged_cost_fails` exhibits a route
     of 3, an upper bound; that 3 is the fewest is computed. K2: attributed
     to the committed 2-term 8-round run (and the 2-term 4-round test), not
     to a 2-term 4-round run the evidence does not contain. §0, §10: the
     third outcome is "neither identified term is bare", not "an assertion
     between them" (two terms each with a loop are also uncleared).
   - `code/tenth/evidence.py`: a dead variable removed, and the local
     `is_addition_kind` replaced by the imported `is_addition`.
