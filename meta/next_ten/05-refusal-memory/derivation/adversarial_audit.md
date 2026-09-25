# Adversarial Audit Report: Problem 05 (Refusal Memory)

**Auditor:** Adversarial Challenger P05  
**Target Problem:** `meta/next_ten/05-refusal-memory`  
**Derivation Directory:** `meta/next_ten/05-refusal-memory/derivation/`  
**Worker:** Worker P05 (`.agents/teamwork/worker_p05/`)  
**Parent Derivation:** Seventeenth (`code/seventeenth/`, `lean4/Seventeenth/`, `paper/seventeenth/`)  
**Initial Verdict:** `REQUEST_CHANGES` (2026-09-24T22:00:00Z)  
**Final Verdict:** **`APPROVE`** (2026-09-24T22:05:00Z)

---

## 1. Executive Summary

We performed an empirical adversarial falsification audit, invariant stress-test, Lean 4 proof verification, and claim hygiene inspection on the derivation artifacts produced for Problem 05 (Refusal Memory).

The discrete mathematical model, BFS exploration, independent census, Lean 4 formalization, and differential evidence pipeline are mathematically sound and exhibit high empirical rigor:
- `model.py` achieves 100% statement and branch coverage.
- `Derivation.lean` compiles with 0 errors, containing zero `sorry`, zero `admit`, zero custom axioms, depending exclusively on standard Lean kernel axioms (`propext`, `Quot.sound`).
- All 5 registered mutation tests bite and induce test suite failures.
- Deterministic evidence regenerates byte-identically under `--check`.
- The candidate falsifier is conclusively refuted across all four configurations, and the hypothesis is confirmed within this toy model.

Both initial blocking findings regarding the repository's Claim Hygiene Rule in `resolution.md` have been fully and independently verified as remediated by Worker P05. Therefore, the final audit verdict is **`APPROVE`**.

---

## 2. Remediation Verification Matrix

| Finding / Item | Pre-Remediation State | Post-Remediation Empirical State | Status |
|---|---|---|---|
| Line 66 in `resolution.md` | Used forbidden term `impossible` | Replaced with compliant phrasing: `precluded in one step from rootA, but reachable in two steps.` | **RESOLVED** |
| Line 93 in `resolution.md` | Used forbidden term `merely` | Replaced with compliant phrasing: `The distinction does not reside solely in an external log:` | **RESOLVED** |
| Claim Hygiene across worker files | 2 violations in `resolution.md` | Automated scan confirms 0 forbidden word violations across all worker markdown files | **VERIFIED** |
| Lean 4 Compilation | Clean | `lean Derivation.lean` compiles with 0 errors, zero `sorry`/`admit`/`axiom` | **VERIFIED** |
| Test Suite & Coverage | Passed | 13/13 passed in 1.1s; 98.92% total coverage, 100% on `model.py` | **VERIFIED** |
| Static Typing | Clean | `python -m mypy --strict` reports 0 issues across all 3 source files | **VERIFIED** |
| Evidence Regeneration | Clean | `python evidence.py --check` confirms byte-identical regeneration | **VERIFIED** |
| Mutation Testing | 5/5 bit | All 5 adversarial mutations bit and induced test failures | **VERIFIED** |

---

## 3. Falsification and Invariant Analysis

### 3.1 The Declared Hypothesis and Falsifier
From `meta/next_ten/05-refusal-memory/why.md`:
- **Hypothesis (open):** *"A refusal record can change later reachability."*
- **Falsifier:** *"Every reached result and round agrees with the seventeenth under both answer readings."*

### 3.2 Empirical Falsification Data
We independently executed the exploration and compared the reached result sets and discovery rounds against parent seventeenth under all four configurations (`bra` $\in \{\text{False}, \text{True}\}$, sameness $\in \{\text{ANCHORED}, \text{FREE}\}$) at bound $N = 3$, rounds $R = 4$:

| Configuration | 17 A-Replace Loops | 17 A-Replace Total | 17 A-Perform Loops (Round) | P05 Refusal Loops (Round) | P05 Refusal Total | Falsifier Status |
|---|---|---|---|---|---|---|
| `bra_False_anchored` | 0 | 51 | 114 (Round 1) | **57 (Round 2)** | 298 | **REFUTED** |
| `bra_False_free` | 0 | 18 | 45 (Round 1) | **37 (Round 2)** | 144 | **REFUTED** |
| `bra_True_anchored` | 0 | 48 | 114 (Round 1) | **59 (Round 2)** | 303 | **REFUTED** |
| `bra_True_free` | 0 | 19 | 49 (Round 1) | **31 (Round 2)** | 144 | **REFUTED** |

### 3.3 Mathematical Logic Chain
1. In parent seventeenth under `A-replace`, obstructed changes are refused and not entered into the closure. Consequently, zero loop-asserting states (`has_xrx = True`) are ever reached from what is given.
2. In parent seventeenth under `A-perform`, obstructed changes are performed immediately upon attempt 1, reaching `oneLoop` (identifying `a` with `b` while `arb` is asserted) in round 1.
3. In Problem 05, the seed adds: *"Its written form is kept with that result; the next attempt at the same written change is performed even if it makes some xrx asserted."*
4. Attempt 1 at an obstructed change (e.g. `identify a and b` or `add ara`) from what is given (`rootA = ⟨givenA, []⟩`) is refused (`StepRM.refusal`), preserving the base graph and recording the change in refusal memory.
5. Attempt 2 at that same written change from the refusal result activates the override step (`StepRM.override`), executing `perform` and producing a state asserting a loop (`two_step_reaches_loop`).
6. Loop states emerge at **round 2**, diverging simultaneously from seventeenth `A-replace` (where loop states never appear) and seventeenth `A-perform` (where loop states appear at round 1 rather than round 2).
7. Therefore, the falsifier is strictly **REFUTED**, and the hypothesis is **CONFIRMED & SUPPORTED** in this model.

---

## 4. Formal Proof Audit (`Derivation.lean`)

- **Lean Compiler Command:** `lean meta/next_ten/05-refusal-memory/derivation/Derivation.lean`
- **Compiler Output:** Clean (exit code 0, 0 warnings, 0 errors).
- **Axiom Audit:**
  - `sorry` / `admit` count: 0 (verified outside comments).
  - Custom `axiom` declarations: 0.
  - Axioms emitted:
    - `Problem05.refusal_preserves_state`: [] (computational `rfl`)
    - `Problem05.refusal_accumulates_record`: [`propext`]
    - `Problem05.two_step_reaches_loop`: [`propext`]
    - `Problem05.two_attempt_difference`: [`propext`, `Quot.sound`]
- **Premise Non-Vacuity & Inhabitation:**
  - `two_step_reaches_loop` explicitly constructs the 2-step witness path:
    $$\text{rootA} \xrightarrow{\text{step1\_ident01\_refusal}} \langle\text{givenA}, [\text{ident01}]\rangle \xrightarrow{\text{step2\_ident01\_override}} \langle\text{perform givenA ident01}, []\rangle$$
  - `rootA_one_step_no_loop` exhaustively cases over all possible transitions from `rootA`, establishing that no 1-step transition can produce a loop.
  - Theorems are constructive and non-vacuous.

---

## 5. Differential Checks and Mutation Testing

We subjected `model.py` to 5 targeted adversarial mutations to verify that the test harness actively bites:

| # | Mutation Description | Target Code Perturbation | Result | Test Failures |
|---|---|---|---|---|
| M1 | Never override (always refuse) | `if c not in s.refused:` $\to$ `if True:` | **BITES (PASS)** | 4 tests failed |
| M2 | Disable obstruction check | `blocked = obstructed_m1(...)` $\to$ `blocked = False` | **BITES (PASS)** | 6 tests failed |
| M3 | Drop change on refusal | `new_refused = s.refused \| {c}` $\to$ `new_refused = s.refused` | **BITES (PASS)** | 3 tests failed |
| M4 | Refusal alters graph state | `RefusalState(s.state, ...)` $\to$ `RefusalState(perform(s.state, c), ...)` | **BITES (PASS)** | 5 tests failed |
| M5 | Invert LOCAL scope on clear | `next_refused = frozenset()` $\to$ `next_refused = s.refused` | **BITES (PASS)** | 3 tests failed |

All 5 mutations were caught immediately by `test_derivation.py`. No checks are vacuous.

---

## 6. Repository Integrity and CI Gate Audit

| Gate / Check | Verification Command | Exit Code | Result Summary |
|---|---|---|---|
| Unit Test Suite | `python -m pytest ... test_derivation.py` | 0 | 13/13 tests pass in 1.1s |
| Coverage Floor | `pytest --cov=... --cov-branch` | 0 | 98.92% total coverage; 100% on `model.py` |
| Static Type Checking | `python -m mypy --strict ...` | 0 | 0 errors across 3 source files |
| Evidence Byte-Identity | `python evidence.py --check` | 0 | Byte-identical regeneration verified |
| Vacuous Checks Gate | `python ci/check_vacuous_checks.py` | 0 | 260 modules scanned, clean |
| Definitional Citations | `python ci/check_definitional_citations.py` | 0 | 267 derived rows, clean |
| Axiom Citations | `python ci/check_axiom_citations.py` | 0 | 21 derivations checked, clean |
| Prose Watchlist | `python ci/check_prose_watchlist.py` | 0 | 22 watched terms, census matches pin |
| Seed Immutability | `git diff --stat -- prompt/` | 0 | Strictly empty |

---

## 7. Conclusion

All requirements of the derivation lifecycle, the Claim Hygiene Rule, and CI integrity standards are fully met. The derivation is certified and approved.
