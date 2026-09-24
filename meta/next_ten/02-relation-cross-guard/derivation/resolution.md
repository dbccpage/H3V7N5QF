# Resolution: Problem 02 (relation-cross-guard)

**Candidate**: C21 (`meta/next_ten/02-relation-cross-guard/`)  
**Derived From**: Ninth derivation (`code/ninth/`, `lean4/Ninth/`, `paper/ninth/`)  
**Author**: Worker P02 (Implementer)  
**Status**: Formal Resolution Completed  

---

## 1. Summary of Hypothesis and Falsifier

- **Hypothesis (from `why.md`)**:
  "A local cross-relation guard breaks independent addition and may still be bypassed by identification."
- **Falsifier (from `why.md`)**:
  "The guarded and ninth result sets agree in every bounded round."

---

## 2. Falsifier Status: Falsified

The falsifier requires that the guarded and ninth result sets agree in every bounded round.
Empirical exploration and differential checks between the ninth system and the guarded system demonstrate that the result sets diverge at round 3:

- **Round 0**: Both systems discover 1 state (empty state `0::`).
- **Round 1**: Both systems discover 1 state (`1::`).
- **Round 2**: Both systems discover 3 states (`2::`, `1::0-0*1|`, `1::|0-0*1`).
- **Round 3**:
  - Ninth system discovers **8** states.
  - Guarded system discovers **7** states.
  - Symmetric difference: `{"1::0-0*1|0-0*1"}` is reached in round 3 of the ninth system by adding `0s0` to `1::0-0*1|`, but is blocked in the guarded system because `0r0` is already asserted.

Because the guarded and ninth result sets diverge at round 3, the falsifier condition is **falsified**.

---

## 3. Hypothesis Status: Confirmed

The hypothesis asserts two coordinated findings:
1. The local cross-relation guard breaks independent addition.
2. The guard can be bypassed by identification.

Both aspects are established through formal derivation, machine-checked Lean 4 verification, and typed Python exploration.

### 3.1 Breaking Independent Addition (Disjoint Support Invariant)

Under the seed modification:
> "Adding `xry` is a change only if `xsy` is not asserted, and adding `xsy` is a change only if `xry` is not asserted."

When changes are restricted to additions (adding terms and adding assertions):
- Any state reached from the empty state maintains disjoint assertion support: for every pair of terms `(x, y)`, at most one relation is asserted (either `r(x, y) = 0` or `s(x, y) = 0`).
- Any attempt to add `xsy` when `xry` is asserted (or `xry` when `xsy` is asserted) is not an admitted change.
- In Lean 4 (`Derivation.lean`), theorem `overlapping_unreachable_by_additions` confirms that any state with overlapping support on a pair (such as `1::0-0*1|0-0*1`) cannot be reached by additions alone.
- In `model.py`, exhaustive exploration over 6 rounds under `additions_only=True` verifies that 100% of reachable states satisfy `is_disjoint_support(s)`.

### 3.2 Bypass by Identification and Cost Elevation

Although overlapping assertions cannot be created directly on the same pair of terms via addition, identification maps distinct terms together:
- By asserting `r` on pair `(u, v)` and `s` on pair `(x, y)` where `(u, v) != (x, y)`, both additions are admitted under the guard.
- A subsequent identification `IDENTIFY u x` and/or `IDENTIFY v y` merges the endpoints, yielding a state where both `r` and `s` are asserted on the same pair.

#### A. Single-Term Overlap Witness (`1::0-0*1|0-0*1`)
- **Ninth cost**: 3 changes (`add_term` -> `add_assertion r 0 0` -> `add_assertion s 0 0`).
- **Guarded cost**: 5 changes.
  1. `add_term` -> `1::`
  2. `add_term` -> `2::`
  3. `add_assertion r 1 1` -> `2::1-1*1|`
  4. `add_assertion s 0 0` -> `2::1-1*1|0-0*1` (disjoint pairs `(1,1)` and `(0,0)`, both admitted)
  5. `identify 0 1` -> `1::0-0*1|0-0*1` (terms merged, placing `r` and `s` on `(0,0)`).
- Machine-checked in Lean 4 (`identification_bypasses_guard`) and verified in `test_one_term_identification_bypass`.

#### B. Two-Term Overlap Witness and Term-Inflation Effect (`2::0-1*1|0-1*1`)
For the two-term state where both `r(0, 1)` and `s(0, 1)` are asserted:
- **Ninth cost**: 4 changes (`add_term` -> `add_term` -> `add_assertion r 0 1` -> `add_assertion s 0 1`).
- **Guarded reachability within `n <= 2`**: Unreachable. Any state with `n <= 2` reached by additions has disjoint support. Any identification on `n <= 2` reduces the term count to `n = 1`, which cannot produce a 2-term state.
- **Guarded reachability with Term Inflation (`n = 3`)**: Reached in 6 changes.
  1. `add_term` -> `1::`
  2. `add_term` -> `2::`
  3. `add_term` -> `3::` (inflates term supply)
  4. `add_assertion r 2 1` -> `3::2-1*1|`
  5. `add_assertion s 0 1` -> `3::2-1*1|0-1*1` (disjoint pairs `(2,1)` and `(0,1)`)
  6. `identify 0 2` -> `2::0-1*1|0-1*1` (contracts term 2 into term 0).
- This establishes that the local cross-relation guard forces temporary term inflation: reaching certain compact overlapping states requires passing through an intermediate state of higher term count before contracting via identification.

---

## 4. Defensible Scope

1. **What this supports**:
   - The cross-relation guard strictly restricts the addition transition graph, rendering overlapping assertions unreachable under additions alone.
   - Identification acts as a non-local bypass, restoring reachability of all ninth states in the presence of term additions and identifications.
   - Reaching overlapping states incurs an additive cost elevation (+2 steps) and, for `n >= 2` terms, requires term inflation.

2. **What this does not support**:
   - It does not support claims of general reachability under fixed finite term bounds: bounded reachability without term inflation fails for states requiring contraction.
   - It does not support unconstrained addition independence in multi-relational structures.
