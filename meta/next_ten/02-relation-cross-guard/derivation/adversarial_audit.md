# Adversarial Audit Report: Problem 02 (relation-cross-guard)

**Target Problem**: `meta/next_ten/02-relation-cross-guard`  
**Auditor**: Challenger P02 (teamwork_preview_challenger)  
**Worker**: Worker P02 (teamwork_preview_worker)  
**Date**: 2026-09-24  
**Verdict**: **APPROVE**  

---

## 1. Executive Summary

This adversarial audit evaluated the formal derivation lifecycle delivered by Worker P02 for Problem 02 (candidate C21, `02-relation-cross-guard`). The audit independently tested the stated hypothesis and falsifier, evaluated claim status discipline, scrutinized Lean 4 proofs for premise vacuity and silent weakening, checked differential evidence checks for vacuity, executed mutation tests, and audited prose against repository watchlists.

### Artifact Evaluation Summary (Claim Hygiene)
1. **What it supports**:
   - The cross-relation guard breaks independent addition, enforcing that any sequence of pure additions from the empty state maintains disjoint relation support ($M_r(x, y) = 0 \lor M_s(x, y) = 0$).
   - Overlapping states (where $M_r(x, y) \ge 1$ and $M_s(x, y) \ge 1$) cannot be reached by additions alone.
   - Vertex identification bypasses the guard, reaching overlapping states by generating disjoint assertions on separate terms and subsequently identifying those terms.
   - Overlapping states incur an additive step cost (+2 steps over the parent ninth derivation), and for $n \ge 2$ terms, require temporary term inflation (expanding to $n+1$ terms before contracting).
2. **What it does not support**:
   - It does not support reachability of compact overlapping states under bounded term counts where $n \le \text{target\_terms}$.
   - It does not support unconstrained addition commutativity in multi-relational graphs.
3. **Narrowest defensible claim**:
   Under the local cross-relation guard, relation overlap is unreachable by additions alone but reachable via term addition and identification, with an elevated shortest path length and an intermediate term-count inflation requirement for multi-term targets.
4. **Next test needed**:
   Evaluate whether a general upper bound of $n + 1$ terms suffices for all $n$-term overlapping states, or if higher term inflation is required for complex multi-edge overlap patterns.

---

## 2. Hypothesis and Falsifier Adversarial Verification

- **Hypothesis**: "A local cross-relation guard breaks independent addition and may still be bypassed by identification."
- **Falsifier**: "The guarded and ninth result sets agree in every bounded round."

### Empirical Falsification Check
The challenger ran independent exploration scripts comparing the parent ninth derivation against the guarded derivation across rounds 0 to 6.
- **Round 0**: 1 state in both systems (`0::`).
- **Round 1**: 1 state in both systems (`1::`).
- **Round 2**: 3 states in both systems (`2::`, `1::0-0*1|`, `1::|0-0*1`).
- **Round 3**:
  - Ninth derivation discovers **8** states.
  - Guarded derivation discovers **7** states.
  - Symmetric difference: `{"1::0-0*1|0-0*1"}` is reached in round 3 of ninth by adding $0s0$ to $1::0-0*1|$, but is blocked under the cross-relation guard because $0r0$ is already asserted.

**Conclusion**: The falsifier is **refuted** by witness `1::0-0*1|0-0*1` at round 3.

### Identification Bypass Check
1. **1-term witness (`1::0-0*1|0-0*1`)**:
   - In ninth: cost 3.
   - In guarded: cost 5 via sequence:
     1. `add_term` -> `1::`
     2. `add_term` -> `2::`
     3. `add_assertion r 1 1` -> `2::1-1*1|`
     4. `add_assertion s 0 0` -> `2::1-1*1|0-0*1` (disjoint pairs $(1, 1)$ and $(0, 0)$)
     5. `identify 0 1` -> `1::0-0*1|0-0*1` (terms merged, placing $r$ and $s$ on $(0, 0)$).
2. **2-term witness and Term Inflation (`2::0-1*1|0-1*1`)**:
   - In ninth: cost 4.
   - In guarded with $n \le 2$: strictly unreachable.
   - In guarded with $n \le 3$: reached in 6 steps via temporary expansion to 3 terms:
     `add_term` -> `add_term` -> `add_term` -> `add_assertion r 2 1` -> `add_assertion s 0 1` -> `identify 0 2`.

**Conclusion**: The hypothesis is **supported** in this setting.

---

## 3. Claim Ledger Discipline Audit

The claim ledger (`claim_ledger.md`) was audited against repository bookkeeping rules:
- **Given**: G1, G2_guard, G3.
- **Chosen**: C1_guard, C2_guard, C3_guard.
- **Derived**: D1_guard, D2_guard, D3_guard, D4_guard, D5_guard, D6_guard.
- **Computed**: K1_guard, K2_guard, K3_guard.
- **Refuted**: R1_guard, R2_guard.
- **Open**: O1_guard.

Every claim possesses an explicit ID, statement, exactly one status, concrete evidence pointer, axiom dependency receipt, re-check citation, and falsification condition. No status inflation was detected.

---

## 4. Formal Proof Audit (`Derivation.lean`)

`Derivation.lean` was inspected and compiled directly using Lean 4.33.1:
1. **Compilation**: Exits with code 0.
2. **Axiom Audit**:
   - Grep search confirms zero occurrences of `sorry`, `admit`, or custom `axiom` declarations.
   - `#print axioms` verifies that all core derivation theorems depend either on no axioms or on standard core Lean axioms (`propext`, `Quot.sound`).
3. **Premise Vacuity Check**:
   - `blocked_pair_cannot_add` checks that `isCrossGuarded s q x y` directly contradicts `s.M (!q) (x, y) = 0`.
   - `reach_add_preserves_disjoint` proceeds by complete structural induction on `ReachG_Add`.
   - `identification_bypasses_guard` constructs concrete witness `s_pre` and verifies `s_post` constructively by decision procedures.
   - No vacuous implications, circular definitions, or silent weakening detected.

---

## 5. Differential Check Non-Vacuity Audit

`evidence.py` defines three distinct differential comparisons:
1. `cmp_ninth`: Compares guarded exploration against unconstrained ninth exploration from `code/ninth/`, confirming round-3 divergence on `1::0-0*1|0-0*1`.
2. `round5_divergence`: Compares guarded exploration with `additions_only=False` against `additions_only=True`, confirming that `1::0-0*1|0-0*1` is reached via identification but not pure additions.
3. `term_inflation_pass`: Compares guarded exploration under $n \le 2$ against $n \le 3$, confirming that `2::0-1*1|0-1*1` requires term inflation.

None of these checks represent vacuous identity or self-comparisons. All compare against independent baseline or restricted models.

---

## 6. Mutation Testing Audit

Mutation testing was executed against `model.py` and evaluated via `test_derivation.py`:
- `mut_no_guard`: Replacing guard check with `return True` -> caught with test failure (exit code 1).
- `mut_disjoint`: Forcing `is_disjoint_support` to ignore overlapping assertions -> caught with test failure (exit code 1).
- `mut_bypass_step`: Mutating the identification step in bypass witness to `ADD_TERM` -> caught with test failure (exit code 1).

All injected mutations were detected and failed the test suite.

---

## 7. Prose Watchlist and Claim Hygiene Audit

1. **Forbidden Words**:
   A regex search for the 14 forbidden hype words defined in the Claim Hygiene Rule returned zero matches across all markdown and code files in `meta/next_ten/02-relation-cross-guard/derivation/`.
2. **Prose Watchlist Census**:
   Auditing with `ci/check_prose_watchlist.py` tokens revealed:
   - `claim_ledger.md`: 0 hits
   - `change_log.md`: 0 hits
   - `resolution.md`: 0 hits
   - `paper.md`: 2 hits on line 175 (`subgraphs`, `morphisms`), located strictly inside Section 6 ("Nearest Known Results and Differences"), adhering to repository isolation standards.

---

## 8. Final Verdict

**VERDICT**: **APPROVE**  
Worker P02's derivation package for Problem 02 meets all criteria under the repository's strict derivation discipline.
