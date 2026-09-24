# Change Log — Problem 07: Two-Term Readings

1. **Plan and pre-derivation setup.**
   - Examined `meta/next_ten/07-two-term-readings/` (`plan.md`, `prompt.md`, `seed_prompt.md`, `why.md`, `diff.patch`).
   - Inherited state and step transition definitions from parent eighteenth derivation (`code/eighteenth/`, `lean4/Eighteenth/`, `paper/eighteenth/`).
   - Identified the seed change: replacement of literal written equality with agreement of records across all readings of at most two terms.

2. **Typed Python model (`model.py`).**
   - Implemented sub-reading extraction: 0-term, 1-term, and 2-term ordered choices.
   - Formalized `record_set` (chosen reading) and `record_multiset` (unchosen alternative).
   - Implemented `same_local` and `same_local_multiset` equivalence checks.
   - Implemented `explore_quotient` tracking round-by-round class discovery.
   - Implemented automated search functions `find_smallest_written_collision` and `find_smallest_free_collision`.
   - Implemented `check_step_congruence` testing transition descent to quotient classes.

3. **Pytest suite (`test_derivation.py`).**
   - Implemented 12 comprehensive unit tests covering:
     - Record extraction correctness and length formula ($1 + n^2$).
     - Equivalence relation properties (reflexive, symmetric, transitive).
     - Smallest written colliding pair ($n=2$, `arb` vs `bra`).
     - Smallest non-isomorphic colliding pair ($n=3$, $s_A$ vs $s_B$).
     - Partition count hierarchy at bound 3 (69 written > 20 FREE canonical > 14 multiset > 8 set).
     - Anchored partition comparison (137 written > 109 canonical > 8 set).
     - Step congruence failure and counterexample inspection.
     - Quotient exploration class discovery.
     - Evidence generation and CLI `--check` verification (including failure paths).
   - Reached 98.82% overall test coverage (above 95% threshold).
   - All tests pass; `mypy --strict` passes with 0 warnings or errors.

4. **Evidence generator (`evidence.py`).**
   - Implemented deterministic generation of `evidence.json`.
   - Integrated `--check` flag supporting byte-identical verification.

5. **Lean 4 formalization (`Derivation.lean`).**
   - Formalized `EdgeConfig`, `LocalRecord`, `LState`, `hasEdge`, `edgeBetween`, `allRecords`, and `LocalEquiv`.
   - Proved that `LocalEquiv` is an equivalence relation (`localEquiv_refl`, `localEquiv_symm`, `localEquiv_trans`).
   - Proved collapsing of distinct written states: `arb_equiv_bra`.
   - Proved collapsing of non-isomorphic states: `s_A_equiv_s_B`.
   - Proved step non-congruence: `s_A_next_not_equiv_s_B_rem1` through `rem4`.
   - Verified clean compilation with Lean 4.33.1 with zero `sorry`, `admit`, or non-standard axioms.

6. **Synthesis and resolution.**
   - Wrote `paper.md` detailing findings, source statuses, quotient hierarchy, and connections to graph reconstruction.
   - Wrote `claim_ledger.md` documenting given, chosen, derived, computed, refuted, and open claims with falsifiers.
   - Wrote `resolution.md` resolving the hypothesis in favor of distinctness and refuting the falsifier.

7. **Adversarial review remediation (Challenger P07).**
   - In `claim_ledger.md`, simplified compound statuses `derived + computed` for Claims D2, D3, D4 to single source status `derived` in accordance with Bookkeeping Rule 1.
   - In `paper.md:135` and `claim_ledger.md:49`, replaced outside-theory term `preorder` with house terminology `reachability relation`.
   - In `resolution.md:58`, replaced outside-theory phrase `induced subgraphs on at most 2 vertices` with seed vocabulary `records across all readings of at most two terms`.
   - Re-verified all gates: 12 tests passing, 98.83% coverage, clean mypy strict typing, byte-identical evidence check, and Lean 4 clean compilation.

8. **Final remediation (Worker R07).**
   - In `claim_ledger.md`, normalized row C2 status from `chosen (alternative)` to single canonical token `chosen` per Bookkeeping Rule 1.
   - In `paper.md`, normalized notion table row `Multiset equality` status to `chosen` (moving `(unchosen alternative)` to description).
   - In `adversarial_audit.md`, replaced verbatim enumeration of forbidden hype words in audit checklist with a summary statement to eliminate false-positive regex matches.
   - Scanned all markdown files in `meta/next_ten/07-two-term-readings/derivation/` with regex for the 14 forbidden hype words, confirming 0 hits across all files.
   - Verified `lean meta/next_ten/07-two-term-readings/derivation/Derivation.lean` exits 0 with 0 errors and zero `sorry`/`admit`/`axiom`.

