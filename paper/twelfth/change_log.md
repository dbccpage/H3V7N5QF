# Change log, twelfth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-twelfth-derivation`.

1. **`CLAUDE.md` gained the twelfth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/twelfth/prompt.md`. The earlier plans above it are unchanged.

2. **Lean: a twelfth library `Twelfth` in the same Lake package, importing
   `Eleventh`; the lakefile gained the target (recorded in
   `paper/change_log.md`).** Targets 1–4 closed: the record of one relation
   is determined by that relation; the two records can differ; an empty
   isolated record is restored by adding a term and a between-assertion
   record is not restored by any one later change; identifying drops a
   term; the ninth's cost/reach/results through the identity; the exchange
   carries records (`recordRel_swap`) and changes (`Step12.swap`); the
   recorded witnesses that C-M2 is not the ninth's count. O2 (other-term
   groups in Lean) is paper plus computation.

3. **Layout: a new package `code/twelfth/` importing from the earlier
   packages only what the identification record leaves intact; no earlier
   module is modified.** Defined afresh: identification records, whether
   they are determined by one relation, restoration, the comparison with
   the ninth, the unchosen recorded exploration.

4. **Bounds lowered relative to the ninth's 5-term run.** Reason: under
   C-M1 the results are the ninth's, already certified at 5 terms with 8
   rounds; record classification is checked on every identification within
   3 terms and 6 rounds (and 2 terms and 8). The recorded reading is at 2
   terms and 5 rounds. Declared in `Plan` and in the paper (C8′).

5. **Watchlist pin for the twelfth paper's final section.** The census
   gained `paper/twelfth/paper.md` (hits of graph-theory terms in §10).
   Reason: the gate tracks every watched hit; the body of the paper has
   none.

6. **Review repairs (pull request #28).** No computed number moved; each
   item corrects a defect found at review.
   - *The count of recorded results on the one-term empty state was wrong in
     the prose.* §0 item 6 and §6/D12 said "two recorded results"; within the
     2-term 5-round bound there are six (one at cost 1, one at cost 3, four at
     cost 5), as `recorded.json` already shows. The prose now states six and
     notes the Lean `recorded_extra` shows only that two of them differ.
   - *The axiom report was missing a cited theorem.* §5/D11 cites
     `recordOf_swap`; `Twelfth/Axioms.lean` had no `#print axioms` line for
     it. One was added and `evidence/twelfth/lean_axioms.txt` regenerated.
   - *Claims narrowed to their evidence.* D3 (the record of a relation is
     read from that relation) and D6 (the record is not a third multiplicity)
     are by construction of C-M1, not emergent; their Lean theorems are
     definitional (`record_determined_by_rel` is `simp [recordRel]` and
     stated for `r`; `no_third_rel` is `rfl`) and are no longer cited as
     proofs. D10 is an identity (the C-M1 exploration wraps the ninth's), so
     only the independent count is a check. D12's `recorded_cost_is_size` is
     a definitional unfold. K2 is attributed to the committed 2-term 8-round
     run, not a 2-term 4-round run the evidence does not contain.
