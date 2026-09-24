# Claim ledger, Problem 09 (Two-Step Leftover)

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `meta/next_ten/09-two-step-leftover/derivation/paper.md`). Lean formalization:
`meta/next_ten/09-two-step-leftover/derivation/Derivation.lean` (namespace `Problem09`).
Axiom report: `propext`, `Classical.choice`, `Quot.sound` only (standard axioms).
Computed files: `meta/next_ten/09-two-step-leftover/derivation/evidence.json`,
written and checked by `meta/next_ten/09-two-step-leftover/derivation/evidence.py`.

The column **Re-check** records how earlier Tenth results were re-checked from this seed.

---

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G-P09 | The seed matches Tenth except for "a sequence of at most two later changes of the four kinds can clear, and a leftover that no such sequence can clear" | given | `diff.patch` against `prompt/tenth/seed_prompt.md` | — | no change elsewhere | a sentence differing elsewhere |
| G-Outcomes | Three leftover outcomes: nothing left, clearable in $\le 2$ changes, uncleared | given | `seed_prompt.md` | — | — | a fourth outcome or different wording |

---

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-L1 | Leftover is recorded on the change, not as a persistent field or third multiplicity | chosen | `model.py` `leftover_of_two_step`; `Derivation.lean` `leftoverTwoStep` | — | 10:C-L1 surviving | a seed sentence placing leftover inside state |
| C-Clear | "Can clear" means reaching a state isomorphic to the start up to term writing | chosen | `model.py` `same`; `Derivation.lean` `EquivState` | — | 10:C-L1 surviving | requiring strict syntactic equality of variable names |
| C-Bounds | Bounds for exploration: (2, 8) and (3, 4) plus 52 edge states | chosen | `model.py` `independent_classification_census` | — | 10:C8' adapted | an infinite or untestable bound |

---

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D-Parity | Every single change modifies size $n+m$ by $\pm 1$; any 2-step sequence has even size delta in $\{-2, 0, +2\}$ | derived | `Derivation.lean` `step_delta_n`, `two_step_term_increase_has_assertion_delta`; `model.py` `parity_analysis` | std | — | a 2-step sequence with odd net size delta |
| D-NoTwoStepId | No identification can be restored in exactly 2 steps | derived | `Derivation.lean` `two_step_cannot_restore_identify`; `model.py` `length_two_restorations == 0` | std | — | an identification restored in exactly 2 steps |
| D-IdEquiv | An identification is 2-step clearable iff it is 1-step clearable | derived | `Derivation.lean` `identify_two_step_iff_one_step`; `model.py` `compare_all_leftovers` | std | — | an identification clearable in 2 steps but not 1 |
| D-RemClear | A removal is clearable in 1 step, hence clearable in at most 2 steps | derived | `Derivation.lean` `removal_restores_in_two`; `model.py` `clearing_sequence_two` | std | 10:D4 re-checked | a removal not restored by re-adding the assertion |
| D-AddNothing | An addition leaves nothing left | derived | `Derivation.lean` `leftoverTwoStep`; `model.py` `leftover_of_two_step` | std | 10:D3 re-checked | an addition leaving a leftover |
| D-Coincide | Two-step leftover classification equals one-step leftover classification across all states and changes | derived | `Derivation.lean` `leftover_two_step_eq_one_step`; computed check in `evidence.json` (21,459 changes evaluated, 0 discrepancies) | std | — | any state and change where 1-step and 2-step classifications disagree |
| D-Falsifier | Every two-step clearable leftover was already one-step clearable | derived | `Derivation.lean` `falsifier_holds`; computed check in `model.py` `verify_falsifier` | std | — | a two-step clearable leftover that is not one-step clearable |
| D-ThreeStep | Three-step clearing does NOT coincide with one-step clearing: 3 steps can clear an identification between non-bare terms | derived | witness derived and computed in `model.py` `three_step_restoration_witness`; `evidence.json` `what_does_not_follow` | — | — | a proof that 3 steps also cannot clear non-bare identifications |

---

## Refuted

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| R-Hypothesis | "Two-step clearing has outcomes beyond the one-step bare-term criterion" | refuted | `Derivation.lean` `falsifier_holds`; `evidence.json` `falsification_results` | std | — | discovery of a state where 2-step clearing succeeds and 1-step clearing fails |

---

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O-GeneralK | Classification of $k$-step clearing for arbitrary even $k \ge 4$ | open | Parity forbids pure $(+1, 0)$ displacement for any even $k$; conjecture that even $k$ never clears identifications of non-bare terms with no loop removals | — | — | a counterexample at $k=4$ |
