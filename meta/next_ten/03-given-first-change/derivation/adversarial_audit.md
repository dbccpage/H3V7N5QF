# Adversarial Audit Report: Problem 03 (Given First Change)

**Auditor:** Adversarial Challenger P03  
**Target:** `meta/next_ten/03-given-first-change/derivation/`  
**Worker:** Worker P03  
**Date:** 2026-09-24  
**Audit Scope:** Empirical falsification verification, Lean 4 proof soundness and non-vacuity, differential check independence, mutation bite, claim hygiene, test coverage, and static typing.

---

## 1. Executive Summary

- **Verdict:** `APPROVE`
- **Confidence:** High
- **Core Hypothesis:** "A given change shifts reachability and cost without a given assertion." -> **CONFIRMED & SUPPORTED**
- **Candidate Falsifier:** "The empty result and one-term result have the ninth's rounds after aligning beginnings." -> **REFUTED**
  - In Problem 03, the beginning is the 1-term state `root03` at round 0 ($\text{cost}_{03} = 0$), differing by 1 from Ninth's round 1.
  - The empty state $\text{empty9}$ ($n = 0$) is completely unreachable in Problem 03 due to the non-emptiness invariant ($n \ge 1$ is inductive across all four permitted changes), so it has no defined round.
  - Therefore, neither the 1-term result nor the empty result exhibits Ninth's rounds after aligning beginnings.

---

## 2. Falsification and Invariant Audit

### 2.1 The Stated Stakes
- **Seed Modification:**
  > *"Given: one change adding a term has been made, and its outcome is the beginning. Nothing else is given."*
- **Parent Ninth Context:**
  Beginning was $\text{empty9} = \text{DState}(0, (), ())$ ($n = 0, m = 0$). The only legal first change was `ADD_TERM`, reaching the 1-term state at round 1. Reachability from $\text{empty9}$ was one-way.
- **Candidate Hypothesis:** *"A given change shifts reachability and cost without a given assertion."*
- **Candidate Falsifier:** *"The empty result and one-term result have the ninth's rounds after aligning beginnings."*

### 2.2 Empirical and Mathematical Findings
1. **Unreachability of the Empty Result:**
   Every legal change in the transition system preserves the non-emptiness of the term set ($n \ge 1$):
   - `ADD_TERM`: $n \to n + 1 \ge 2 > 0$.
   - `IDENTIFY`: requires $n \ge 2$ distinct terms; replaces two terms by one, yielding $n - 1 \ge 1 > 0$.
   - `ADD_ASSERTION` ($r$ or $s$): leaves $n$ invariant ($n \ge 1$).
   - `REMOVE_ASSERTION` ($r$ or $s$): leaves $n$ invariant ($n \ge 1$).
   Because the beginning state `root03` has $n = 1 > 0$, by mathematical induction no state with $n = 0$ is ever reachable. The empty state $\text{empty9}$ is strictly excluded from results.

2. **Reachability Shift and Mutual Reachability:**
   In Ninth, reachability from the empty state was strictly one-way (in-degree 0). In Problem 03, the empty state is eliminated, and for any two well-formed states $s, t$ with $s.n \ge 1$ and $t.n \ge 1$:
   - $s$ reaches a 1-term state via assertion removals and term identifications.
   - The 1-term state reaches $t$ via term additions and assertion additions.
   Thus, reachability among all reachable states is mutual (strongly connected).

3. **Cost Shift of Exactly -1:**
   Because each change alters state size ($\text{size} = n + m$) by at most 1, and `size(root03) = 1`, reaching state $t$ requires at least $\text{size}(t) - 1$ changes. A sequence of $t.n - 1$ term additions followed by $t.m$ assertion additions reaches $t$ in exactly $\text{size}(t) - 1$ steps:
   $$\text{cost}_{03}(t) = \text{size}(t) - 1$$
   In Ninth, the cost was $\text{cost}_{\text{ninth}}(t) = \text{size}(t)$.
   Thus, for every reachable state:
   $$\text{cost}_{03}(t) - \text{cost}_{\text{ninth}}(t) = -1$$
   For the empty state, $\text{cost}_{\text{ninth}}(\text{empty9}) = 0$, but in Problem 03 the cost is undefined/None because it is unreachable.

4. **Refutation of the Falsifier:**
   - One-term result: round 0 in Problem 03 vs. round 1 in Ninth.
   - Empty result: unreachable in Problem 03 vs. round 0 in Ninth.
   Neither result has Ninth's rounds after aligning beginnings. The candidate falsifier is strictly refuted.

5. **Confirmation of the Hypothesis:**
   The seed provides zero given assertions ($m = 0$), yet reachability shifts (empty state excluded, topology becomes strongly connected) and cost shifts ($-1$ across all reachable states). The hypothesis is supported in this model.

---

## 3. Formal Proof Audit (`Derivation.lean`)

- **Lean Version:** Lean 4 (version 4.33.1).
- **Execution Command:** `lean meta/next_ten/03-given-first-change/derivation/Derivation.lean`
- **Compiler Result:** Exit code 0, 0 errors, 0 warnings.
- **Axiom Audit:**
  - Automated regex search for `sorry`, `admit`, `axiom`: **0 matches**.
  - Kernel `#print axioms`:
    - `DState.empty_not_reachable_from_root03`: depends only on standard Lean kernel axioms `[propext, Quot.sound]`.
    - `DState.empty_not_result03`: depends only on `[propext, Quot.sound]`.
    - `DState.falsifier_refuted`: depends only on `[propext, Quot.sound]`.
    - `DState.hypothesis_supported_empty_excluded`: depends only on `[propext, Quot.sound]`.
- **Proof Structure and Non-Vacuity:**
  - `root03` is explicitly defined as `addTerm empty`, proved to have $n = 1$, $m = 0$, size 1, and well-formedness.
  - `step_nonempty`: proved by exhaustive case analysis over the 6 step constructors (`addTerm`, `addR`, `addS`, `removeR`, `removeS`, `identify`), verifying $n > 0$ preservation.
  - `reach_nonempty`: proved by structural induction on `Reach`, showing any path from a nonempty state terminates in a nonempty state.
  - `empty_not_reachable_from_root03`: constructively refutes reachability to `empty` ($n = 0$) by contradiction against $n > 0$.
  - The proofs contain no circular definitions, vacuous implications, or silent weakenings.

---

## 4. Differential Checks and Orbit Oracle Audit (`evidence.py`)

- **Differential Mechanism:**
  `evidence.py` and `model.py` implement an independent completeness oracle using the cycle index polynomial of the symmetric group $S_n$ acting on ordered pairs (Burnside orbit counts via `ninth.orbits.count_results`).
- **Disagreement Sensitivity:**
  The BFS exploration independently traverses reachable states by generating transitions up to bound $B = 3$ terms and $R = 4$ rounds (145 states). The counts in each $(n, m)$ cell are checked against `counts_within(bound=3, rounds=4)`.
  - Disagreements across all 13 cells: **0**.
  - Total expected results: 145.
  - Total explored results: 145.
  - Empty state explored: False.
- **Non-Vacuous Comparison:**
  `test_verify_exploration_completeness_mismatch` in `test_derivation.py` injects a synthetic empty state into the exploration depth table and verifies that `verify_exploration_completeness` catches the anomaly (`complete == False`, `empty_explored == True`, `"0/0" in disagreements`).
- **Evidence Regeneration (`--check`):**
  Command `python meta/next_ten/03-given-first-change/derivation/evidence.py --check` was executed and returned `Byte-identical regeneration verified` with exit code 0.

---

## 5. Mutation Testing and Test Bite Verification

We subjected `model.py` to an adversarial mutation matrix across 6 distinct semantic sites:

| Mutation Description | Mutation Code Injection | Test Suite Response | Bite Result |
|---|---|---|---|
| Mutate GIVEN_SIZE to 0 | `GIVEN_SIZE: int = 0` | FAILED (`AssertionError` in `test_cost_and_cost_shift`) | **BITE** |
| Mutate GIVEN_SIZE to 2 | `GIVEN_SIZE: int = 2` | FAILED (`AssertionError` in `test_cost_and_cost_shift`) | **BITE** |
| Mutate `reachable` to always True | `return True` | FAILED (`AssertionError` in `test_reachability`) | **BITE** |
| Mutate `cost` to omit offset | `return state.size` | FAILED (`AssertionError` in `test_cost_and_cost_shift`) | **BITE** |
| Mutate `added` to ignore offset | `return state.n, state.m` | FAILED (`AssertionError` in `test_added_metrics`) | **BITE** |
| Mutate `is_beginning` to $n=0$ | `state.n == 0 and state.m == 0` | FAILED (`AssertionError` in `test_beginning_properties`) | **BITE** |

**Mutation Score:** 6/6 mutations killed (100% kill rate). The test suite exhibits true sensitivity to logical regressions.

---

## 6. Static Typing and Test Coverage

- **Mypy Strict:**
  Command: `python -m mypy --strict meta/next_ten/03-given-first-change/derivation/model.py meta/next_ten/03-given-first-change/derivation/test_derivation.py meta/next_ten/03-given-first-change/derivation/evidence.py`
  Result: `Success: no issues found in 3 source files` (exit code 0).
- **Pytest Suite:**
  Command: `python -m pytest meta/next_ten/03-given-first-change/derivation/test_derivation.py --no-cov -v`
  Result: 12 passed in 1.23s.
- **Coverage:**
  - `model.py`: 100% line coverage (156/156), 100% branch coverage (50/50).
  - `evidence.py`: 100% line coverage (82/82), 100% branch coverage (16/16).
  - `test_derivation.py`: 99% line coverage (163/164).
  - Combined derivation package coverage: **99.58%**, meeting the $\ge 95\%$ requirement.

---

## 7. Claim Hygiene and Watchlist Audit

- **Prose Watchlist:**
  Scanned using `ci/check_prose_watchlist.py`:
  - `paper.md`: Exactly 2 hits (`polya` and `digraphs` at line 196), both situated strictly within Section 9 ("Nearest Known Results"), in full accordance with repository rules. Zero outside-theory hits in the paper body.
  - `resolution.md`, `claim_ledger.md`, `change_log.md`: **0 hits**.
- **Forbidden Words Census:**
  Automated regex scanning across all markdown files for the 14 forbidden hype words (per the repository Claim Hygiene Rule):
  - Total hits: **0**.
- **Claim Discipline:**
  Every claim in `claim_ledger.md` has an assigned status (`given`, `chosen`, `derived`, `computed`, `refuted`), concrete evidence, explicit falsification conditions, and re-check references. Zero ungrounded or open claims.

---

## 8. Audit Conclusion and Final Recommendation

Worker P03 has delivered a mathematically rigorous, fully tested, self-contained derivation package for Problem 03. All native gates pass, all mutations bite, the Lean 4 formalization compiles cleanly without axioms or sorry, and the empirical falsification check definitively refutes the candidate falsifier and supports the candidate hypothesis.

**Final Verdict:** `APPROVE`
