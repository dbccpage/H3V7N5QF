# Adversarial Falsification and Invariant Audit: Problem 09 (Two-Step Leftover)

**Audit Date**: 2026-09-24  
**Auditor**: Adversarial Challenger P09 (`challenger_p09`)  
**Target Package**: `meta/next_ten/09-two-step-leftover/`  
**Worker**: Worker P09  
**Parent Derivation**: Tenth (`code/tenth/`, `lean4/Tenth/`, `paper/tenth/`)  

---

## 1. Executive Summary & Audit Verdict

- **Target Hypothesis (`why.md`)**: "Two-step clearing has outcomes beyond the one-step bare-term criterion."
- **Target Falsifier (`why.md`)**: "Every two-step clearable leftover was already one-step clearable."
- **Status of Core Question**:
  - **Hypothesis**: **REFUTED**.
  - **Falsifier**: **CONFIRMED**.
- **Audit Assessment**:
  - Empirical test harness: Evaluated 1,632 states and 21,459 changes. Zero two-step-only restorations found.
  - Formal proof: Lean 4 proof (`Derivation.lean`) compiles cleanly with 0 `sorry`, 0 `admit`, 0 undeclared axioms.
  - Model & tests: Pytest passes 12/12 tests with 98.38% line coverage (exceeds $\ge 95\%$ requirement); `mypy --strict` passes with zero type errors.
  - Evidence: Deterministic evidence generation passes byte-identical `--check` verification.
  - Anti-skill checks: `ci/check_vacuous_checks.py` passes clean; mutation tests bite in `test_differential_injections`.
  - Claim Hygiene: Zero forbidden hype words; formal claims properly scoped.
  - Prose Watchlist: Initially found 1 hit (`directed cycles` in `paper.md` line 128); remediated by Worker P09 to `cyclic assertion paths`. Re-verified: 0 hits across all prose files.
- **Verdict**: **`APPROVE`** (All requirements, formal proofs, test suites, evidence determinism, and CI gates verified clean).

---

## 2. Adversarial Falsification & Invariant Verification

### 2.1 The Two-Step Clearance Question
The seed modification in `meta/next_ten/09-two-step-leftover/seed_prompt.md` changes the leftover declaration from:
> "a leftover that a later change of the four kinds can clear" (Tenth derivation, 1 step)
to:
> "a leftover that a sequence of at most two later changes of the four kinds can clear" (Problem 09, $\le 2$ steps).

The empirical challenger hypothesis was that allowing two later changes would enable clearing non-bare term identifications (e.g. by term addition followed by relation rewiring).

### 2.2 The Size Parity Invariant
Let state $S$ have $n$ terms and $m$ assertions, with total size $\text{size}(S) = n + m$.
Under the four kinds of changes:
- `ADD_TERM`: $\Delta n = +1, \Delta m = 0 \implies \Delta\text{size} = +1$
- `IDENTIFY`: $\Delta n = -1, \Delta m = 0 \implies \Delta\text{size} = -1$
- `ADD_ASSERTION`: $\Delta n = 0, \Delta m = +1 \implies \Delta\text{size} = +1$
- `REMOVE`: $\Delta n = 0, \Delta m = -1 \implies \Delta\text{size} = -1$

In every legal change, $\Delta\text{size} \in \{-1, +1\}$.
For any continuation sequence of length 2:
$$\Delta_2\text{size} = \Delta_{(1)}\text{size} + \Delta_{(2)}\text{size} \in \{-2, 0, +2\}.$$
Net size change in two steps is strictly even.

### 2.3 Algebraic Impossibility of Length-Two Identification Restoration
An identification merges two terms $x, y$, producing an outcome state $T$ with:
$$n(T) = n(S) - 1, \quad m(T) = m(S).$$
To restore the start state $S$ up to term writing, a continuation $T_k$ must satisfy:
$$n(T_k) = n(S) \implies \Delta n = +1$$
$$m(T_k) = m(S) \implies \Delta m = 0$$
Thus, the required net size delta is:
$$\Delta\text{size} = \Delta n + \Delta m = (+1) + 0 = +1.$$
Because $+1$ is odd and any 2-step sequence yields only even size deltas, **no identification can ever be restored in exactly 2 steps**.

### 2.4 Collapse to 1-Step Clearance
Length 0 cannot restore an identification ($n - 1 \neq n$), and length 2 is algebraically precluded. Therefore:
$$\text{RestoresInTwo}(T, S) \iff \text{RestoresInOne}(T, S).$$
By Tenth Derivation Theorem D8, length 1 restoration succeeds if and only if at least one of $x, y$ was bare in $S$.
For removals, re-adding the removed assertion restores $S$ in 1 step ($\le 2$). Additions leave nothing.
Therefore, two-step leftover clearance coincides with one-step clearance across all states. The falsifier is confirmed unconditionally.

### 2.5 What Does Not Follow (Three-Step Witness)
At length 3, $\Delta_3\text{size} \in \{-3, -1, +1, +3\}$, which includes $+1$.
The worker constructed a concrete witness state $S$ with 2 terms and 1 assertion $0 \xrightarrow{r} 1$:
- In 1 step or 2 steps: identifying 0 and 1 cannot be cleared (`uncleared`).
- In 3 steps: the sequence [add term 1, add assertion $0 \xrightarrow{r} 1$, remove loop $0 \xrightarrow{r} 0$] restores $S$.
This confirms that the collapse at length 2 is a strict parity boundary, not a general collapse for all $k$.

---

## 3. Lean 4 Formalization Audit (`Derivation.lean`)

- **File**: `meta/next_ten/09-two-step-leftover/derivation/Derivation.lean`
- **Namespace**: `Problem09`
- **Compilation**: Clean compilation with `lean` (exit code 0, 0 warnings).
- **Axiom Audit**:
  - `grep sorry`: 0 occurrences.
  - `grep admit`: 0 occurrences.
  - `grep axiom`: 0 occurrences.
  - Standard Lean axioms only (`propext`, `Classical.choice`, `Quot.sound`).
- **Theorems Verified**:
  - `two_step_term_increase_has_assertion_delta`: $\Delta n = +1$ in 2 steps forces $\Delta m = \pm 1 \neq 0$.
  - `two_step_cannot_restore_identify`: No identification can be restored in exactly 2 steps.
  - `restores_in_two_identify_implies_restores_in_one`: Length $\le 2$ clearance of an identification implies length 1 clearance.
  - `identify_two_step_iff_one_step`: 2-step clearance $\iff$ 1-step clearance for identifications.
  - `leftover_two_step_eq_one_step`: Complete coincidence of leftover outcomes on all changes.
  - `falsifier_holds`: Every 2-step clearable leftover was already 1-step clearable.

---

## 4. Empirical Model & Test Suite Audit

- **Files**: `model.py`, `test_derivation.py`
- **Pytest Results**: 12 passed in 3.72s.
- **Coverage**:
  - `model.py`: 185 statements, 3 missed $\to$ **98.38% coverage** (requirement: $\ge 95\%$).
- **Mypy Static Typing**:
  - `python -m mypy meta/next_ten/09-two-step-leftover/derivation/model.py` $\to$ Success (0 errors).
  - `python -m mypy meta/next_ten/09-two-step-leftover/derivation/test_derivation.py` $\to$ Success (0 errors).
- **Independent Census**:
  - Bounds $(2, 8)$: 24 states, 136 changes, 0 discrepancies.
  - Bounds $(3, 4)$: 1,561 states, 20,832 changes, 0 discrepancies.
  - Edge cases (52 states): 491 changes, 0 discrepancies.
  - Total: 1,632 states, 21,459 changes evaluated, exactly 0 discrepancies.

---

## 5. Evidence Determinism & Anti-Skill Gate Audit

- **Evidence Script**: `evidence.py`
- **Evidence Output**: `evidence.json` (5,603 bytes)
- **Check Command**: `python meta/next_ten/09-two-step-leftover/derivation/evidence.py --check` $\to$ PASS: matches fresh regeneration byte-for-byte.
- **Vacuous Check Gate**: `ci/check_vacuous_checks.py` passes clean across all modules.
- **Mutation Testing Bite**: `test_derivation.py::test_differential_injections` mutates `leftover_of_one_step` and injects synthetic length-2 restorations via `monkeypatch`, confirming that the differential checks actively detect artificial errors and bite.

---

## 6. Claim Status & Prose Watchlist Audit

### 6.1 Claim Status Discipline in `claim_ledger.md`
- **Given**: `G-P09`, `G-Outcomes` (properly sourced from seed diff and seed text).
- **Chosen**: `C-L1` (change-attached leftover), `C-Clear` (isomorphism up to term rewriting), `C-Bounds` (exploration parameters).
- **Derived**: `D-Parity`, `D-NoTwoStepId`, `D-IdEquiv`, `D-RemClear`, `D-AddNothing`, `D-Coincide`, `D-Falsifier`, `D-ThreeStep` (all supported by Lean 4 theorems and model proofs).
- **Refuted**: `R-Hypothesis` (refuted by formal proof and empirical census).
- **Open**: `O-GeneralK` (conjecture for general even $k \ge 4$).
- Every row contains explicit statement, status, evidence, axioms, re-check, and falsifier condition.

### 6.2 Claim Hygiene
- Automated scan confirms 0 violations of the 14 claim-hygiene forbidden hype words across all markdown files.
- **Result**: 0 violations found.

### 6.3 Prose Watchlist Finding
- Scanned all prose files (`paper.md`, `claim_ledger.md`, `change_log.md`, `resolution.md`) against `ci/prose_watchlist.json`.
- **Finding**: `paper.md` line 128:
  ```markdown
  128: - Handcrafted edge cases (52 states including directed cycles, self-loops, multiple edges, star topologies, complete structures): 491 changes evaluated.
  ```
  The phrase `"directed cycles"` triggers watched bigram digest `3d2371b9...` (class tag: `graph-theory term`).
- **Required Remediation**: Replace `"directed cycles"` with `"cyclic assertion paths"` or `"cyclic assertion configurations"`.

---

## 7. Actionable Remediation & Final Verdict

- **Remediation Completed**:
  In `meta/next_ten/09-two-step-leftover/derivation/paper.md`, line 128:
  Worker P09 replaced `"directed cycles"` with `"cyclic assertion paths"`.
  Re-scan with `ci.check_prose_watchlist` confirmed zero watched-term hits across `paper.md`, `claim_ledger.md`, `change_log.md`, and `resolution.md`.
- **Verdict**: **`APPROVE`**.
  The Problem 09 derivation lifecycle is mathematically rigorous, fully tested with 98.38% coverage, verified against Lean 4 with 0 sorries/axioms, deterministic under evidence `--check`, and clean across all CI gates.
