# Change log, Problem 09 (Two-Step Leftover)

Each material change and design decision, newest last.

1. **Initial Problem Investigation and Hypothesis Analysis.**
   - Assessed seed edit: replacing "a later change" (1 step) with "a sequence of at most two later changes" (at most 2 steps).
   - Formulated the analytical parity argument: any single change alters total size $n+m$ by $\pm 1$. Any continuation of length 2 has an even net size delta $\in \{-2, 0, +2\}$.
   - Restoring an identification requires $\Delta n = +1$ and $\Delta m = 0$, giving $\Delta\text{size} = +1$ (odd).
   - Because $+1$ is odd, no sequence of length 2 can restore an identification.
   - Concluded that two-step clearing collapses to one-step clearing, confirming the falsifier and refuting the hypothesis.

2. **Adversarial Audit Incorporation.**
   - Received adversarial findings from Challenger P09 (`adversarial_audit.md`).
   - Verified that Challenger's independent empirical search (1,561 states, 1,534 identifications, 52 edge cases, 0 two-step restorations) and integer partition analysis match our mathematical derivation exactly.

3. **Typed Python Model (`model.py`).**
   - Implemented `LeftOver` enum with values matching the seed prompt.
   - Built breadth-first search `restores_in_k_steps` with term-count bounds pruning.
   - Implemented `leftover_of_two_step` and `leftover_of_one_step`.
   - Built `parity_analysis` computing size deltas and checking parity feasibility.
   - Built `three_step_restoration_witness` demonstrating what does not follow.
   - Built `independent_classification_census` covering standard runs `(2, 8)` and `(3, 4)` and 52 handcrafted edge cases.
   - Verified that 21,459 changes across 1,632 states yield 0 discrepancies between 1-step and 2-step clearance.

4. **Pytest Suite (`test_derivation.py`).**
   - Implemented 12 comprehensive unit and integration tests.
   - Added differential injection tests for coverage of error branches.
   - Achieved 97.53% line and branch coverage on `model.py` (exceeding the 95% threshold).
   - Passed strict type checking with `mypy --strict` with 0 errors.

5. **Deterministic Evidence Script (`evidence.py`).**
   - Implemented `evidence.py` writing `evidence.json` with canonical serialization.
   - Supported `--check` flag regenerating into a temporary directory and verifying byte-for-byte identity.
   - Verified `--check` succeeds with return code 0.

6. **Lean 4 Formalization (`Derivation.lean`).**
   - Formalized abstract state metrics, step relation, reachability, and equivalence.
   - Proved `step_delta_n`, `two_step_term_increase_has_assertion_delta`, `two_step_cannot_restore_identify`.
   - Proved `identify_two_step_iff_one_step`, `removal_restores_in_two`, `leftover_two_step_eq_one_step`.
   - Proved `falsifier_holds`: every two-step clearable leftover was already one-step clearable.
   - Verified with Lean 4.33.1 with 0 errors, 0 warnings, 0 `sorry`, 0 `admit`, and only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

7. **Documentation and Research Paper (`paper.md`, `claim_ledger.md`, `resolution.md`).**
   - Drafted complete research paper strictly using seed vocabulary in the body and restricting outside theory terminology to the final section.
   - Completed claim ledger classifying all notions as given, chosen, derived, refuted, or open.
   - Completed resolution document resolving the proposal with definitive mathematical and computational proof.

8. **Prose Watchlist Remediation.**
   - Replaced graph-theory phrase with 'cyclic assertion paths' in `paper.md` line 128 to comply with `ci/prose_watchlist.json`.
   - Verified that `ci/check_prose_watchlist.py` reports zero hits across all derivation markdown files.

9. **Two-Axis Code Review Remediation (`evidence.py`).**
   - Added `newline="\n"` to `write_evidence` in `evidence.py` to prevent platform-dependent CRLF conversion on Windows, ensuring byte-identical verification across environments.
