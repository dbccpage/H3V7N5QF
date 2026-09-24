# Change log, fifteenth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-fifteenth-derivation`.

1. **`CLAUDE.md` gained the fifteenth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/fifteenth/prompt.md`. The earlier plans above it are unchanged.

2. **Lean: a fifteenth library `Fifteenth` in the same Lake package, importing
   `Fourteenth`; the lakefile gained the target (recorded in
   `paper/change_log.md`).** Targets 1–4 closed: admission records
   (`reaching`, `admitted`); reaching does not admit
   (`reaching_does_not_admit`); every reached result can be admitted
   (`every_reached_can_be_admitted`); admission is not an assertion and not
   a kind; admission of `r` is admission of `s` as records of a result;
   the ninth's cost/reach/results through the identity; the exchange keeps
   the admission record (`admission_swap`, `Step15.swap`); the tagged
   witnesses that C-A2 is not the ninth's count. O2 (`Step9` to
   `Admission`) is paper: `Step9` is a `Prop`.

3. **Layout: a new package `code/fifteenth/` importing from the earlier
   packages only what admission-not-given-by-reaching leaves intact; no
   earlier module is modified.** Defined afresh: admission records, whether
   they are assertions of either relation, whether every reached result can
   be admitted, whether admission of one relation constrains the other, the
   comparison with the ninth, the unchosen tagged exploration.

4. **Bounds lowered relative to the ninth's 5-term run.** Reason: under
   C-A1 the results are the ninth's, already certified at 5 terms with 8
   rounds; admission classification is checked on every performed change
   within 3 terms and 6 rounds (and 2 terms and 8). The tagged reading is
   at 2 terms and 5 rounds. Declared in `Plan` and in the paper (C8′).

5. **Watchlist pin for the fifteenth paper's final section.** The census
   gained `paper/fifteenth/paper.md` (hits of graph-theory terms in §10).
   Reason: the gate tracks every watched hit; the body of the paper has
   none.

6. **Review repairs (pull request #31).** No committed number moved; each
   item corrects a defect found at review.
   - *The cross-relation check compared a value with a copy of itself.*
     `check_admissions` compared `admission_of_reaching(arrived)` with the
     record it had already computed from the same function on the same state,
     so it could not disagree. It now compares each result's record with the
     record of its `r/s` exchange (`swap`), which a relation-dependent record
     would break; a test drives it with such a record.
   - *Two injection tests never called the code under test.* In
     `test_compare_with_ninth_notices` the lost-result case removed a result
     and asserted only its own change; it now calls `compare_with_ninth` and
     asserts the missing result and the failed independent count.
   - *Claims narrowed to their evidence.* The admission model is a constant
     under the chosen reading C-A1 (reaching leaves not-admitted; every
     result can be admitted; the record names no relation), so D3–D8 are by
     construction, not derived; their Lean theorems are definitional
     (`reaching_does_not_admit`, `admission_not_a_kind`, `r_admission_is_s`,
     `admission_swap` are `reaching = .notAdmitted` or `x = x`; `no_third_rel`
     is `rfl`) and are no longer cited as proofs. "Every reached result can be
     admitted" (D6) is the chosen reading C-A1, not a derived fact; its Lean
     `every_reached_can_be_admitted` is the C-A2 record constructor. D10 is an
     identity (the C-A1 exploration wraps the ninth's), so only the
     independent count is a check. D12's `tagged_cost_fails` is an upper bound
     (a route of 2); the minimum of 2 is computed. §8's items are refuted by
     the chosen reading rather than given absent or mismatched witnesses.

7. **Definitional-citation gate.** The gate flagged D11's ledger row for
   citing `admission_swap`/`admission_swap_admitted` (`reaching = reaching`,
   `admitted = admitted`) as *derived*; the row now discloses that the
   exchange-keeps-record part is definitional (matching the paper §5).

## Whole-repo review repairs (2026-09-23)

- F009: printed two cited Fourteenth witnesses and regenerated the Lean report and manifest. F012: admission availability in given.json now calls the model function, with an injected drift test; regenerated evidence. No claim or theorem statement changed.
