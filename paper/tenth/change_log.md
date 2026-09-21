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
