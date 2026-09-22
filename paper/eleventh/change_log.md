# Change log, eleventh derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-eleventh-derivation`.

1. **`CLAUDE.md` gained the eleventh derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/eleventh/prompt.md`. The earlier plans above it are unchanged.

2. **Lean: an eleventh library `Eleventh` in the same Lake package, importing
   `Tenth`; the lakefile gained the target (recorded in
   `paper/change_log.md`).** Targets 1–4 closed: injective writings determine;
   a collision forbids coarser writings; a collision of one relation need not
   be a collision of the other; identifying drops a term and writing does not;
   the ninth's cost/reach/results through the identity; the exchange carries
   determination (`determines_swap`) and changes (`Step11.swap`); the labeled
   witnesses that C-W2 is not the ninth's count. O2 (reading a determining
   collision is not identifying) is paper plus computation.

3. **Layout: a new package `code/eleventh/` importing from the earlier
   packages only what writing leaves intact; no earlier module is
   modified.** Defined afresh: writings, determination, coarser writings,
   the comparison with the ninth, the unchosen labeled exploration.

4. **Bounds lowered relative to the ninth's 5-term run.** Reason: under
   C-W1 the results are the ninth's, already certified at 5 terms with 8
   rounds; writing classification is checked on every explored result
   within 3 terms and 6 rounds (and 2 terms and 8). The labeled reading is
   at 2 terms and 4 rounds. Declared in `Plan` and in the paper (C8′).

5. **Watchlist pin for the eleventh paper's final section.** The census
   gained `paper/eleventh/paper.md` (one hit of the graph-theory term in
   §10). Reason: the gate tracks every watched hit; the body of the paper
   has none.

6. **Review repairs (pull request #27).** No committed number moved (the
   two-term evidence is unchanged); each item corrects a defect found at
   review.
   - *The labeled reading (C-W2) over-counted at three or more terms.*
     `labeled_of` paired a state with every restricted-growth writing, so
     writings related by the state's own automorphisms — the same result up
     to how the terms are written — were counted separately (the bare
     three-term state gave five, not three). It now returns one writing per
     orbit under the state's automorphisms (`writing.py` `writing_orbits`);
     the bell-sum cross-check, which merely re-summed the same per-writing
     count, is replaced by an independent Burnside orbit count
     (`orbit_count_burnside`, flag `labeled_equals_orbit_count`). At two
     terms every writing is its own orbit, so the committed two-term
     evidence is unchanged.
   - *Two injection tests never called the code under test.* In
     `test_compare_with_ninth_notices` the shifted-round and lost-result
     cases changed the exploration and asserted only their own change. They
     now call `compare_with_ninth` and assert the round disagreement, the
     missing result and the failed independent count.
   - *Claims narrowed to their evidence.* D6 is by construction of C-W1, not
     a Lean theorem (`no_third_rel` is `rfl` and mentions no writing). D10 is
     an identity (the C-W1 exploration wraps the ninth's), so only the
     independent count is a check. D8's `collide_keeps_terms` is a card fact
     that a writing does not change (a writing is not a state operation).
     D12's "two results" is the computed `labeled_of`; the Lean `labeled_extra`
     illustrates rather than proves it, and `labeled_cost_is_size` is a
     definitional unfold. K2 is attributed to the committed 2-term 8-round
     run, not a 2-term 4-round run the evidence does not contain.
   - *The reading of "determines" recorded its alternative.* §3 now names the
     weaker term-by-term reading and eliminates it (it does not make the
     assertions recoverable from the writing), rather than leaving it
     unstated.
