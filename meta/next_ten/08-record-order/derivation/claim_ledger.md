# Claim Ledger: Problem 08 (Record-Order)

| ID | Statement | Status | Evidence | Axiom Report | Falsifier / Test |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **C1** | Leftovers are recorded in sequence order upon assertion removal. | given | `model.py:remove_assertion`, `test_derivation.py:test_transitions_add_remove_admit` | N/A | Failure to append to leftover sequence |
| **C2** | Only the most recently recorded leftover is admissible for admission into $r$ or $s$. | derived | `model.py:admit_top`, `Derivation.lean:isAdmissible`, `test_derivation.py:test_lifo_admission_blocking` | Standard (`propext`) | Admitting a non-top leftover |
| **C3** | An unadmitted leftover is not an assertion of either relation. | given | `model.py:OrderedState.size`, `test_derivation.py:test_empty_and_basic_state` | N/A | Leftover counted in relation multiplicity |
| **C4** | Forgetting sequence order yields sixteenth's multiset counted record via projection $\pi$. | derived | `model.py:to_sixteenth_counts`, `Derivation.lean:toCount`, `evidence.py` | None | Disagreement between count and frequency |
| **C5** | Two records with identical count projections can have disjoint admissible next steps. | derived | `Derivation.lean:witness_different_admissions`, `evidence.py:witness.json` | Standard (`propext`) | Identical admission sets for all same-count states |
| **C6** | The result quotient of the ordered model strictly refines sixteenth's quotient. | computed | `model.py:compare_quotients`, `evidence.py:summary.json` (388 ordered vs 386 sixteenth) | Standard (`propext`) | All sixteenth classes remain singletons |
| **C7** | The falsifier "all bounded results are classified by the old count alone" is refuted. | refuted | `Derivation.lean:falsifier_refuted`, `test_derivation.py:test_minimal_quotient_witness` | Standard (`propext`) | Absence of any split class in bounded exploration |
| **C8** | The hypothesis "order-sensitive feedback changes the result quotient and admission paths" is supported. | derived | `resolution.md`, `evidence.py:witness.json`, `Derivation.lean:falsifier_refuted` | Standard (`propext`) | Falsifier holds across all depths |
| **C9** | Term permutations rename endpoints of leftovers while preserving sequence order. | chosen | `model.py:rewrite`, `test_derivation.py:test_rewrite_and_canonical` | N/A | Permutation reorders stack positions |
| **C10** | Identifying terms $u < v$ preserves the sequence order of the leftover record while remapping endpoints. | derived | `model.py:identify_terms`, `test_derivation.py:test_identify_preserves_leftover_order_and_remaps` | N/A | Leftovers reordered by identification |
