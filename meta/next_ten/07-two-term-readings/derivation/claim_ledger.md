# Claim Ledger — Problem 07: Two-Term Readings

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**.
"core" means the cited theorem depends only on Lean 4 core logic without non-standard axioms.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1 | The eighteenth seed with the sameness sentence replaced by: "A reading names at most two terms and records the assertions between them. Two results are the same if every such reading gives the same record." | given | `meta/next_ten/07-two-term-readings/seed_prompt.md` | — | 18:G1 reworded | A differing sentence in the seed |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C1 | A reading is an ordered choice of at most two terms; sameness compares sets of induced records. Bound: 3 terms, 12 rounds | chosen | `model.py:extract_records`, `model.py:record_set` | — | 18:C1 replaced | An explicit seed directive to compare multisets or label terms |
| C2 | Unchosen alternative: comparing multisets of local reading records | chosen | `model.py:record_multiset` | — | — | Proof that multisets produce identical partitions to sets |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1 | Local reading equality (`LocalEquiv`) is an equivalence relation: reflexive, symmetric, and transitive | derived | `Derivation.lean:localEquiv_refl`, `localEquiv_symm`, `localEquiv_trans` | core | — | A state where reflexivity, symmetry, or transitivity fails |
| D2 | At $n = 2$, `arb` and `bra` are distinct written states but have identical local record sets | derived | `Derivation.lean:arb_equiv_bra`, `model.py:find_smallest_written_collision` | core | 18:D2 | `same_local(s_arb, s_bra)` returning False |
| D3 | At $n = 3$, non-isomorphic states $s_A$ (2 assertions) and $s_B$ (4 assertions) have identical local record sets | derived | `Derivation.lean:s_A_equiv_s_B`, `model.py:find_smallest_free_collision` | core | 1:FREE | A term permutation mapping $s_A$ to $s_B$, or differing record sets |
| D4 | The one-step transition system does not descend to equivalence classes: step congruence fails | derived | `Derivation.lean:s_A_next_not_equiv_s_B_rem1`..`rem4`, `model.py:check_step_congruence` | core | Rule-5 re-check | Proof that every step from $s_A$ can be matched from $s_B$ up to equivalence |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | At bound 3, 69 written states partition into 69 written, 20 FREE canonical, 14 multiset, and 8 set classes | computed | `evidence.json`, `test_derivation.py:test_partition_hierarchy_bound_3` | — | Computed against `eighteenth.explore` and `xry.state` | A regenerated exploration yielding different class counts |
| K2 | Exhaustive verification identifies 31 step transition mismatches across the 69 states at bound 3 | computed | `evidence.json`, `model.py:check_step_congruence` | — | — | A re-run finding 0 transition failures |
| K3 | Evidence regenerates byte-identically under `--check` | computed | `python evidence.py --check` exit code 0 | — | — | `--check` returning non-zero |

## Refuted

| ID | Statement Refuted | Status | Evidence | Axioms | Re-check | What would falsify the refutation |
|---|---|---|---|---|---|---|
| R1 | Local reading sameness agrees with written equality | refuted | D2, K1 | core | 18:C1 | All 69 written states having pairwise distinct record sets |
| R2 | Local reading sameness agrees with FREE rewriting | refuted | D3, K1 | core | 1:C4 | All 20 FREE canonical classes having pairwise distinct record sets |
| R3 | Step transitions form a congruence with local reading equivalence | refuted | D4, K2 | core | Rule-5 step check | Proof of bisimulation or step congruence |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would close it |
|---|---|---|---|---|---|---|
| O1 | Closed-form formula for the number of local reading record classes for arbitrary term bound $n$ | open | Section 7 of paper | — | — | A general combinatorial formula verified against small $n$ |
| O2 | Exact reachability relation structure induced on quotient classes by multistep paths | open | Section 7 of paper | — | — | An explicit finite automaton or directed graph of quotient reachability |
