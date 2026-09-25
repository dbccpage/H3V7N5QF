# Adversarial Audit Report: Problem 07 (Two-Term Readings)

**Target Problem**: `meta/next_ten/07-two-term-readings`  
**Worker**: Worker P07 (`meta/next_ten/07-two-term-readings/derivation/`)  
**Auditor**: Adversarial Challenger P07 (`.agents/teamwork/challenger_p07/`)  
**Verdict**: **`APPROVE`**

---

## 1. Executive Summary

We performed an empirical adversarial falsification audit and invariant stress-test of the Problem 07 (`two-term-readings`) derivation artifacts.

The derivation is **formally rigorous, empirically validated, and fully compliant** across all dimensions:
1. **Hypothesis Resolution**: The hypothesis (*"Sameness by local readings differs from both written equality and FREE rewriting"*) is **confirmed in this model**. At bound 3 terms and 12 rounds, the 69 reachable written states partition into 69 written classes, 20 FREE canonical classes, 14 multiset local reading classes, and 8 set local reading classes ($69 > 20 > 14 > 8$). The falsifier (*"The bounded partitions agree with one of the parent's two equivalences"*) is **refuted**.
2. **Witnesses**:
   - Smallest written collision at $n = 2$: `arb` vs `bra` ($s_{\text{arb}} \neq s_{\text{bra}}$ written, yet identical local record set). Proved in Lean 4 (`arb_equiv_bra`).
   - Smallest non-isomorphic collision at $n = 3$: $s_A$ (2 assertions, one 2-cycle) vs $s_B$ (4 assertions, two 2-cycles) have $|E(s_A)| = 2 \neq 4 = |E(s_B)|$, yet yield the identical 4-element local record set. Proved in Lean 4 (`s_A_equiv_s_B`).
3. **Step Non-Congruence**: Formally proved in Lean 4 (`s_A_next_not_equiv_s_B_rem1`..`rem4`) and verified computationally (31 transition failures detected across 69 states).
4. **Lean 4 Proofs**: Compiled cleanly with zero errors, zero warnings, and zero occurrences of `sorry`, `admit`, or declared axioms.
5. **Mutation Testing**: 5 distinct semantic mutations were applied to `model.py`, and **all 5 mutations were killed** by the test suite (100% kill rate).
6. **Code Coverage & Types**: 98.83% line & branch coverage; `mypy --strict` passes with 0 issues. Evidence regenerates byte-identically under `--check`.
7. **Claim Hygiene**: Zero forbidden hype words found.
8. **Remediations Verified**:
   - Compound statuses in `claim_ledger.md` for claims D2, D3, D4 were updated to single source status `derived` (satisfying Bookkeeping Rule 1).
   - Outside-theory vocabulary outside Section 8 was eliminated: `paper.md:135` and `claim_ledger.md:49` now use house terminology (`reachability relation`), and `resolution.md:58` uses seed terminology (`records across all readings of at most two terms`).

---

## 2. Verification of Remediations

### 2.1 Single Claim Status Discipline in `claim_ledger.md`
- **Audit Check**: Re-inspected claims D2, D3, D4 in `claim_ledger.md`.
- **Result**: **PASS**. Each claim now carries exactly one source status (`derived`). Computational evidence is properly cited in the `Evidence` column.

### 2.2 Prose Watchlist Compliance
- **Audit Check**: Scanned all markdown files in `meta/next_ten/07-two-term-readings/derivation/` against `ci/prose_watchlist.json`.
- **Result**: **PASS**. Zero outside-theory words appear in `claim_ledger.md`, `resolution.md`, or Sections 1–7 of `paper.md`. The only occurrences of literature terms are in Section 8 ("Nearest Known Results and Differences") of `paper.md`, as permitted by repository contract.

---

## 3. Empirical Verification Results

### 3.1 Unit Testing & Coverage
- Command:
  ```bash
  python -m pytest -o addopts="" --cov=meta/next_ten/07-two-term-readings/derivation --cov-branch --cov-report=term-missing meta/next_ten/07-two-term-readings/derivation/test_derivation.py
  ```
- Result: **PASS** (12 passed in 3.53s).
- Line & Branch Coverage:
  - `evidence.py`: 97%
  - `model.py`: 99%
  - `test_derivation.py`: 99%
  - **Total**: **98.83%** (exceeds 95% requirement).

### 3.2 Static Type Checking
- Command:
  ```bash
  python -m mypy --strict meta/next_ten/07-two-term-readings/derivation/model.py meta/next_ten/07-two-term-readings/derivation/evidence.py meta/next_ten/07-two-term-readings/derivation/test_derivation.py
  ```
- Result: **PASS** (`Success: no issues found in 3 source files`).

### 3.3 Byte-Identical Evidence Regeneration
- Command:
  ```bash
  python meta/next_ten/07-two-term-readings/derivation/evidence.py --check
  ```
- Result: **PASS** (`PASS: Evidence verified byte-identically.`, exit code 0).

### 3.4 Lean 4 Formalization
- Command:
  ```bash
  lean meta/next_ten/07-two-term-readings/derivation/Derivation.lean
  ```
- Result: **PASS** (exit code 0, 0 errors, 0 warnings).
- Grep Audit for `sorry|admit|axiom`: 0 matches found.

### 3.5 Mutation Testing (Empirical Bite)
5 semantic mutations were applied to `model.py` and run against `test_derivation.py`:
1. *Mutation 1* (Omit backward edge check in 2-term reading): **KILLED**
2. *Mutation 2* (Omit 0-term reading): **KILLED**
3. *Mutation 3* (Omit 1-term reading): **KILLED**
4. *Mutation 4* (Replace set equality with multiset equality in `same_local`): **KILLED**
5. *Mutation 5* (Trivially return True in `same_local`): **KILLED**
- Result: **100% Kill Rate (5/5 killed)**.

### 3.6 Claim Hygiene Rule
- Automated scan for the 14 forbidden hype words defined in the Claim Hygiene Rule: **0 violations found**.

---

## 4. Final Verdict

**`APPROVE`**

All requirements, mathematical contracts, and gate criteria for Problem 07 (`meta/next_ten/07-two-term-readings/derivation/`) are fully satisfied. The derivation package is verified and approved.
