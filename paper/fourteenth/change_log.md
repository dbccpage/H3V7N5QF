# Change log, fourteenth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-fourteenth-derivation`.

1. **`CLAUDE.md` gained the fourteenth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/fourteenth/prompt.md`. The earlier plans above it are unchanged.

2. **Lean: a fourteenth library `Fourteenth` in the same Lake package, importing
   `Thirteenth`; the lakefile gained the target (recorded in
   `paper/change_log.md`).** Targets 1–4 closed: leftover writings
   (`leftoverAdd`, `leftoverRemove`, `leftoverIdentify`); leftover of a
   removal ignores the relation (`leftover_remove_r_s`, both `Step9.remove`
   on `twoBoth`); leftover is not an assertion and not an answer; clearing
   leftover is not one of the four kinds; the ninth's cost/reach/results
   through the identity; the exchange carries leftover of additions and
   removals (`leftover_swap_addTerm`, `leftover_swap_remove`, `Step14.swap`);
   the tagged witnesses that C-F2 is not the ninth's count. O2 (`Step9` to
   `LeftWriting`) is paper: `Step9` is a `Prop`.

3. **Layout: a new package `code/fourteenth/` importing from the earlier
   packages only what leftover-as-writing leaves intact; no earlier
   module is modified.** Defined afresh: leftover writings, whether they
   are assertions of either relation, whether leftover of one relation is
   leftover of the other, the comparison with the ninth, the unchosen
   tagged exploration.

4. **Bounds lowered relative to the ninth's 5-term run.** Reason: under
   C-F1 the results are the ninth's, already certified at 5 terms with 8
   rounds; leftover classification is checked on every performed change
   within 3 terms and 6 rounds (and 2 terms and 8). The tagged reading is
   at 2 terms and 5 rounds. Declared in `Plan` and in the paper (C8′).

5. **Watchlist pin for the fourteenth paper's final section.** The census
   gained `paper/fourteenth/paper.md` (hits of graph-theory terms in §10).
   Reason: the gate tracks every watched hit; the body of the paper has
   none.

6. **Review repairs (pull request #30).** The tagged (C-F2) count moves from
   130 to 131; each item corrects a defect found at review.
   - *The tagged reading numbered the leftover tag inconsistently with the
     result.* `tagged_perform` canonicalized the result state but kept the
     leftover tag in the pre-change numbering, so it merged and split tagged
     results wrongly and named absent terms. The state and the tag's terms
     are now renumbered together (`state.py` `canonical_tagged`). An
     identification's tag keeps only the surviving term (`∼u`), the other
     being gone from the result. The 2-term 5-round count becomes 131
     (extra 30), matching an independent joint-canonical recount.
   - *The D5 witness used a non-change.* `given.json` removed `0 s 1` from a
     state asserting nothing in `s`, which is not a change. The witness now
     asserts the pair in both relations, so both removals are legal; the
     cross-relation check in `invariants.py` is guarded by `has(...)` so it
     compares two real changes.
   - *The axiom report was missing cited theorems.* `twoBoth_remove_r` and
     `twoBoth_remove_s` (§0.4/D5) had no `#print axioms` line;
     `Fourteenth/Axioms.lean` now reports them and
     `evidence/fourteenth/lean_axioms.txt` was regenerated.
   - *Claims narrowed to their evidence.* D5, D7 and D4 are by construction
     (the pair writing names no relation; the state has no leftover field; no
     answer field); their Lean theorems are definitional (`leftover_remove_r_s`
     is `x = x`; `no_third_rel` is `rfl`; `leftover_not_answer` is a
     tautology) and are no longer cited as proofs. D10 is an identity (the
     C-F1 exploration wraps the ninth's), so only the independent count is a
     check. D12's `tagged_cost_fails` is an upper bound (a route of 3); the
     minimum of 3 is computed. §8's D5 item is refuted, not given a bogus
     holding witness.

7. **Definitional-citation gate.** The gate flagged D11's ledger row for
   citing `leftover_swap_addTerm` (`leftoverAdd = leftoverAdd`) as *derived*;
   the row now discloses that the exchange-carries-leftover part is
   definitional (matching the paper §5, which already said so).
