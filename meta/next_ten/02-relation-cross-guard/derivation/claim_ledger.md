# Claim Ledger: Problem 02 (relation-cross-guard)

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open** (see `paper.md`).  
Lean formalization: `Derivation.lean` in namespace `Derivation02`.  
Axiom report: `evidence/lean_axioms.txt`.  
"std" denotes reliance only on standard core Lean axioms (`propext`, `Quot.sound`); "none" denotes zero axiom dependencies. No `sorry`, `admit`, or declared axioms occur in the formalization.

---

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1 | Sentences of the ninth seed: terms written with letters; two relations `r` and `s`; multiplicities; adding/removing assertions | given | `prompt/ninth/seed_prompt.md`; `seed_prompt.md` | — | Ninth G1, G2 no change | A seed sentence stating different primitives |
| G2_guard | Adding `xry` is a change only if `xsy` is not asserted, and adding `xsy` is a change only if `xry` is not asserted | given | `meta/next_ten/02-relation-cross-guard/seed_prompt.md`; `diff.patch` | — | New in Problem 02 | A seed sentence dropping or altering the guard condition |
| G3 | Nothing is given: to begin with there are no terms and nothing is asserted | given | `seed_prompt.md` | — | Ninth G3 no change | A seed sentence giving initial terms or assertions |

---

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C1_guard | "Not asserted" means multiplicity zero. The guard checks whether `other_rel(x, y) == 0` | chosen | `model.py` (`can_add_assertion`); `Derivation.lean` (`StepG.addAssertion`) | — | Re-checked against ninth semantics | A reading where not asserted means something other than multiplicity 0 |
| C2_guard | Admitted changes: IDENTIFY, REMOVE, ADD_TERM, and guarded ADD_ASSERTION. Ordering: identifications, removals, term addition, guarded additions | chosen | `model.py` (`guarded_changes`) | — | Ninth C5, C6 with cross-guard | A different ordering convention |
| C3_guard | Finite bounds for systematic exploration: terms `n <= 3`, assertions `m <= 3`, rounds 6 | chosen | `model.py` (`explore`); `evidence.py` | — | Ninth C8 adapted to 3 terms | A run under different bound parameters |

---

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1_guard | `StepG` embeds into `Step9`: every guarded step is an admitted ninth step | derived | `Derivation.lean` (`StepG.toStep9`); `model.py` | none | Ninth Step9 re-checked | A guarded step that is not a valid ninth step |
| D2_guard | The guard blocks addition: if `xsy` is asserted, adding `xry` is not admitted | derived | `Derivation.lean` (`blocked_pair_cannot_add`); `test_derivation.py` | none | Ninth comparison | An admitted addition where the other relation is present |
| D3_guard | Pure additions preserve disjoint assertion support: every state reached from empty by additions alone has disjoint `r` and `s` pairs | derived | `Derivation.lean` (`reach_add_preserves_disjoint`); `model.py` | none | Re-proved for guarded additions | An addition sequence producing overlapping assertions |
| D4_guard | Overlapping states cannot be reached by additions alone | derived | `Derivation.lean` (`overlapping_unreachable_by_additions`) | none | Re-proved | An addition-only path reaching an overlapping state |
| D5_guard | Identification bypasses the guard: `1::0-0*1\|0-0*1` is reachable in 5 steps via term addition, disjoint assertions, and identification | derived | `Derivation.lean` (`identification_bypasses_guard`); `model.py` | std | Re-checked against model | Failure of the 5-step sequence to produce the target state |
| D6_guard | Two-term overlap requires term inflation: reaching `2::0-1*1\|0-1*1` cannot occur within `n <= 2`, requiring expansion to `n = 3` before contracting | derived | `model.py` (`witness_two_term_bypass`); `test_derivation.py`; computed check in `evidence/differential.json` | std | Re-checked against model | A valid path within `n <= 2` reaching the target |

---

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1_guard | Divergence from ninth derivation at round 3: ninth discovers 8 states, guarded discovers 7 states; symmetric difference is `{"1::0-0*1\|0-0*1"}` | computed | `evidence/differential.json`; `test_comparison_with_ninth_and_falsifier` | — | Differential check against ninth | Equal discovery counts at round 3 |
| K2_guard | Frontier and state census: within `n <= 3, m <= 3`, 284 distinct states are discovered in 6 rounds; 133 attempts exit via declared bounds | computed | `evidence/run.json`; `evidence/frontier.json` | — | Independent BFS exploration | A different state count within declared bounds |
| K3_guard | Disjoint support census: 280 of 284 discovered states have disjoint support; 4 states exhibit overlapping support via identification bypass | computed | `evidence/disjoint_counts.json` | — | Independent census | Discrepancy in disjoint support classification |

---

## Refuted

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| R1_guard | The falsifier condition ("The guarded and ninth result sets agree in every bounded round") is refuted | refuted | Witness `1::0-0*1\|0-0*1` at round 3; `differential.json` | — | Direct round-3 comparison | Agreement of discovery sets at round 3 |
| R2_guard | Overlapping states can be generated by pure additions from empty | refuted | `Derivation.lean` (`overlapping_unreachable_by_additions`); `test_disjoint_support_invariant` | none | Invariant preservation proof | A valid addition sequence reaching an overlapping state |

---

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O1_guard | Minimal term inflation bound: whether reaching an arbitrary overlapping state on `n` terms requires at most `n + 1` terms | open | Model exploration suggests `n + 1` suffices for `n in {1, 2}`; general `n` unproved | — | Open problem | A counterexample state on `n` terms requiring `n + 2` or more terms |
