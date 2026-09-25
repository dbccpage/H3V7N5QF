# Resolution: Problem 09 (Two-Step Leftover)

**Target Problem**: `meta/next_ten/09-two-step-leftover/`  
**Parent Derivation**: Tenth (`prompt/tenth/`, `code/tenth/`, `lean4/Tenth/`, `paper/tenth/`)  
**Resolution Date**: 2026-09-24  

---

## 1. The Core Question

From `why.md`:
- **Hypothesis (Open)**: "Two-step clearing has outcomes beyond the one-step bare-term criterion."
- **Falsifier**: "Every two-step clearable leftover was already one-step clearable."
- **Drop / Rewrite Condition**: "Drop or rewrite the proposal if its edited seed has an unresolved contradiction, if every new distinction sits only in an external log or chosen label, if the finite test finds the stated falsifier and no distinct claim remains, or if its required state/step map cannot be made precise without a third seed sentence."

---

## 2. Verdict: Hypothesis Refuted, Falsifier Confirmed

The proposal is definitively resolved:
- **Hypothesis Status**: **REFUTED**.
- **Falsifier Status**: **CONFIRMED**.
- **Verdict**: The proposal confirms the stated falsifier. Allowing a sequence of at most two later changes yields zero new clearable outcomes beyond the one-step bare-term criterion. The one-step and two-step leftover classifications coincide across all legal states and all four kinds of changes.

---

## 3. Mathematical Proof of Resolution (Size Parity Invariant)

Let $S$ be a state with $n$ terms and total assertion multiplicity $m$. Its total size is $\text{size}(S) = n + m$.

1. **Step Parity**: Every change of the four kinds alters size by $\pm 1$:
   - `ADD_TERM`: $\Delta n = +1, \Delta m = 0 \implies \Delta\text{size} = +1$.
   - `IDENTIFY`: $\Delta n = -1, \Delta m = 0 \implies \Delta\text{size} = -1$.
   - `ADD_ASSERTION`: $\Delta n = 0, \Delta m = +1 \implies \Delta\text{size} = +1$.
   - `REMOVE`: $\Delta n = 0, \Delta m = -1 \implies \Delta\text{size} = -1$.

2. **Even Net Size Delta in Two Steps**:
   In any sequence of two changes $T \to T_1 \to T_2$, the net change in size is:
   $$\Delta_2\text{size} = \Delta_{(1)}\text{size} + \Delta_{(2)}\text{size} \in \{-2, 0, +2\}.$$
   It is strictly an even integer.

3. **Restoration Requirement for Identification**:
   An identification $S \xrightarrow{\text{identify } x, y} T$ merges two terms, yielding $n(T) = n(S) - 1$ and $m(T) = m(S)$.
   To restore $S$ up to term writing, a continuation $T_k$ must achieve:
   $$\Delta n = n(T_k) - n(T) = +1 \quad \text{and} \quad \Delta m = m(T_k) - m(T) = 0.$$
   Consequently, the net required change in size is:
   $$\Delta\text{size} = \Delta n + \Delta m = (+1) + 0 = +1.$$

4. **Impossibility of Length-Two Identification Restoration**:
   Because $+1$ is odd and two steps produce only even net size changes, no sequence of length 2 can achieve $\Delta\text{size} = +1$.
   Therefore, no identification can be restored in exactly two steps.
   (Formalized and proved in Lean 4: `Problem09.two_step_cannot_restore_identify`).

5. **Collapse to Length-One Restoration**:
   Because length 0 cannot restore an identification ($n - 1 \neq n$) and length 2 is algebraically precluded, any sequence of at most two changes restoring an identification must have length 1.
   A single change can restore an identification if and only if one of the two identified terms was bare (Tenth derivation Theorem D8).
   For removals, re-adding the removed assertion restores the start in 1 step, which is $\le 2$ steps.
   For additions, the change leaves nothing (`nothing left`).

Therefore:
$$\text{leftoverTwoStep}(S, C) = \text{leftoverOneStep}(S, C) \quad \text{for all } S \text{ and all } C.$$
(Formalized and proved in Lean 4: `Problem09.leftover_two_step_eq_one_step` and `Problem09.falsifier_holds`).

---

## 4. Empirical Falsification Evidence

The exhaustive empirical verification executed in `model.py` and recorded in `evidence.json` confirms the analytical deduction:
- Total states evaluated: 1,632 (including standard exploration bounds (2, 8) and (3, 4), and 52 handcrafted edge-case states).
- Total changes evaluated: 21,459.
- Identifications evaluated: 1,534.
- Discrepancies between one-step and two-step clearance: **0**.
- Identifications cleared in exactly two steps: **0**.
- All runs coincide: **True**.

---

## 5. What Does Not Follow (Sharp Boundary at Three Steps)

The non-triviality of the multi-step clearance problem is demonstrated by showing that the collapse does **not** extend to three steps:
- A sequence of 3 changes **can** clear an identification between two non-bare terms.
- **Witness**: Let $S$ have two terms $0, 1$ with one assertion $0 \xrightarrow{r} 1$ (neither term is bare).
  - Identification $C = \text{identify}(0, 1)$ yields $T$ with one term $0$ and self-loop $0 \xrightarrow{r} 0$.
  - In 1 step: UNCLEARED (restores_1 = False).
  - In 2 steps: UNCLEARED (restores_2 = False).
  - In 3 steps: CLEARABLE (restores_3 = True) via the sequence:
    1. `add a term` (adds term 1 as bare)
    2. `add arb` (adds $0 \xrightarrow{r} 1$)
    3. `remove ara` (removes loop $0 \xrightarrow{r} 0$)
    Outcome: exactly restores $S$.
  Because 3 is odd, parity allows net size delta $+1$ (e.g. $+1 + 1 - 1 = +1$).

---

## 6. Artifact Verification Summary

1. `model.py`: Fully typed model implementing 1-step, 2-step, and 3-step clearance, term-count pruning, and census generation. Checked with `mypy --strict` (0 errors).
2. `test_derivation.py`: Pytest suite with 12 tests, differential injection coverage. Achieved 97.53% line and branch coverage (above 95% requirement).
3. `evidence.py`: Deterministic evidence script with `--check` verification passing byte-for-byte.
4. `Derivation.lean`: Lean 4 formalization proving the parity invariant and the falsifier theorem without `sorry`, `admit`, or undeclared axioms. Checked with Lean 4.33.1 (exit code 0).
5. `paper.md`, `claim_ledger.md`, `change_log.md`: Clean documentation adhering to claim hygiene and seed prose discipline.

**Conclusion**: The proposal for Problem 09 is fully resolved with the confirmation of the falsifier.
