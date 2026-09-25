# Adversarial Audit Report: Problem 01 (Remove Bare Term)

**Auditor:** Adversarial Challenger P01  
**Target:** `meta/next_ten/01-remove-bare-term/derivation/`  
**Worker:** Worker P01  
**Date:** 2026-09-24  
**Audit Scope:** Falsification verification, Lean 4 proof rigor, differential check independence, mutation bite, claim hygiene, test coverage, and static typing.

---

## 1. Executive Summary

- **Verdict:** `APPROVE`
- **Confidence:** High
- **Core Hypothesis:** "A bare-term removal destroys the empty state's one-way reachability." -> **CONFIRMED & SUPPORTED**
- **Candidate Falsifier:** "No nonempty result reaches the empty beginning within two changes." -> **REFUTED** (Concrete 1-step return from nonempty result $\text{oneTermBare}$, and 2-step cycle from `empty`).

---

## 2. Falsification and Cycle Stress-Test

### 2.1 The Stated Stakes
- **Seed addition:** *"removing a term that names no assertion deletes that term and nothing asserted."*
- **Parent Seventh behavior:** Every transition from a state with terms leaves a state with terms (`Step7.nonempty`). The empty state has in-degree 0; transitions out of `empty` are one-way.
- **Candidate falsifier:** *"No nonempty result reaches the empty beginning within two changes."*

### 2.2 Empirical and Formal Findings
1. **Concrete Counterexample to Falsifier:**
   - From `empty = State(0, ())`:
     $$\text{empty} \xrightarrow{\text{ADD\_TERM}} \text{oneTermBare} = \text{State}(1, (0,))$$
   - In $\text{oneTermBare}$, $n = 1 > 0$ (the state is nonempty).
   - Multiplicity for term 0 is zero in all directions: $M(0, 0) = 0$. Hence, term 0 is bare.
   - Performing $\text{REMOVE\_BARE\_TERM}(0)$ on $\text{oneTermBare}$ deletes term 0, yielding `empty`:
     $$\text{oneTermBare} \xrightarrow{\text{REMOVE\_BARE\_TERM}(0)} \text{empty}$$
   - This transition takes **1 change** ($1 \le 2$).
   - The candidate falsifier is strictly **REFUTED**.

2. **The 2-Step Cycle:**
   $$\text{empty} \to \text{oneTermBare} \to \text{empty}$$
   - Path length from `empty` back to `empty`: **2 changes**.
   - Lean theorem `empty_returns_in_two_steps` and `two_step_cycle` formally certify this cycle without axioms.
   - Python test `test_two_step_cycle` and artifact `evidence/cycle_witness.json` independently compute and verify it.

3. **Hypothesis Confirmation:**
   - The empty state has incoming transitions from nonempty states (in-degree $\ge 1$).
   - The empty state can be repeatedly exited and re-entered.
   - One-way reachability of the empty state is destroyed.
   - Furthermore, every state $s$ can reach `empty` by clearing assertions ($s.m$ steps) and deleting bare terms ($s.n$ steps), rendering the state space strongly connected.

---

## 3. Formal Proof Audit (`Derivation.lean`)

- **Compiler Command:** `lean meta/next_ten/01-remove-bare-term/derivation/Derivation.lean`
- **Compiler Result:** Exit code 0, 0 errors, 0 warnings.
- **Axiom Audit:** Grep for `sorry`, `admit`, `axiom` yielded 0 occurrences.
- **Premise Vacuity:**
  - `removeBare_wf`: Hypotheses `s.WF` and `s.isBare t` are satisfied by witness `(oneTermBare, 0)`. The premise is genuinely inhabited.
  - `falsifier_refuted`: Proved constructively with witness `oneTermBare`.
  - `empty_state_in_degree_positive`: Proved constructively with witness `oneTermBare`.
- **Proof Rigor:** No circular definitions; all inductive step definitions match the seed specification.

---

## 4. Test Suite, Typing, and Coverage

- **Pytest:**
  `python -m pytest meta/next_ten/01-remove-bare-term/derivation/test_derivation.py -o addopts="" --cov=meta/next_ten/01-remove-bare-term/derivation --cov-branch`
  - Result: 16 passed in 4.94s.
  - Overall coverage: **98.70%** (exceeds 95% threshold).
  - Module breakdown:
    - `model.py`: 99% line & branch coverage.
    - `evidence.py`: 96% line & branch coverage.
    - `test_derivation.py`: 100% coverage.
- **Mypy:**
  `python -m mypy --strict meta/next_ten/01-remove-bare-term/derivation/model.py meta/next_ten/01-remove-bare-term/derivation/evidence.py meta/next_ten/01-remove-bare-term/derivation/test_derivation.py`
  - Result: `Success: no issues found in 3 source files` (exit code 0).

---

## 5. Differential Checks and Mutation Bite Audit

### 5.1 Differential Checks
- Executed: `python ci/check_vacuous_checks.py --code C:/Users/a343o/source/repos/H3V7N5QF/meta/next_ten/01-remove-bare-term/derivation`
- Result: Clean (3 modules scanned, 0 self-comparisons).
- Checks in `evidence.py`:
  1. `step_counts_formula_matches_changes`: Verified that $C(n, 2) + d + b + 1 + n^2$ matches actual changes generated across all states.
  2. `two_term_closed_form_matches_burnside`: Closed form matches general Burnside orbit count for $m=0..10$.
  3. `size_changes_by_plus_minus_one`: Invariant $\Delta \text{size} = \pm 1$ holds for every change.
  4. `bare_term_removal_preserves_counted_assertions`: Multiplicity sum $m$ invariant under bare-term removal.
  5. `cost_equals_bfs_depth`: Closed-form cost matches BFS shortest path depth.

### 5.2 Mutation Bite Testing
1. **Omission Mutation:** Forbidding `REMOVE_BARE_TERM` restores in-degree 0 on `empty`. Verified in test suite.
2. **Invalid Term Mutation:** Attempting to remove an asserted term as bare raises `ValueError`. Verified in test suite.
3. **Index Shift Mutation:** Tested removal of term 0 when higher terms have self-loops ($s = \text{State}(3, (0, 0, 0, 0, 2, 0, 0, 0, 1))$). Outcome verified: $n \to 2$, multiplicities shift down accurately to $(2, 0, 0, 1)$, total $m=3$ preserved.

---

## 6. Deterministic Evidence Regeneration

- Generation command: `python meta/next_ten/01-remove-bare-term/derivation/evidence.py`
- Check command: `python meta/next_ten/01-remove-bare-term/derivation/evidence.py --check`
- Result: Byte-identical regeneration verified (`MANIFEST.sha256` verified).

---

## 7. Claim Hygiene and Prose Watchlist Audit

- **Forbidden Words Scan:** Scanned all markdown files in `meta/next_ten/01-remove-bare-term/derivation/` against the 14 repository-defined forbidden hype words specified in Claim Hygiene.
  - Result: **0 violations found.**
- **Prose Watchlist:** Scanned against `ci/prose_watchlist.json`.
  - Result: **0 unpinned outside-theory terms found.**
- **Summary Checklist:** Included in `paper.md` and `resolution.md` with:
  1. What it supports
  2. What it does not support
  3. Narrowest defensible claim
  4. Next test needed

---

## 8. Minor Notes for Future Standardization

- In `claim_ledger.md`, claims P01-4, P01-5, and P01-7 are strictly labeled `derived` under single-status discipline, with computational verification recorded in the evidence column.

---

## 9. Final Conclusion

Problem 01 (Remove Bare Term) satisfies all scientific, formal, empirical, and stylistic requirements. The derivation shows in this model that bare-term removal destroys the one-way reachability of the empty state and refutes the candidate falsifier with an explicit 1-step counterexample and 2-step cycle.

**Verdict:** `APPROVE`
