import Eighth.Rename

/-!
# What every theorem cited by the eighth paper rests on

`python code/lean_report_eighth.py` runs this file and stores the output in
`evidence/eighth/lean_axioms.txt`.  Every theorem cited in `paper/eighth/` is
listed: those of the eighth library (`Seed.Eighth`), and those of the earlier
derivations that the eighth paper cites and re-checks.
-/

-- Eighth/State: two relations, the projections, the embedding, the beginnings
#print axioms Seed.Eighth.ext_proj
#print axioms Seed.Eighth.proj_addTerm
#print axioms Seed.Eighth.proj_addAssertion_self
#print axioms Seed.Eighth.proj_addAssertion_other
#print axioms Seed.Eighth.proj_remove_self
#print axioms Seed.Eighth.proj_remove_other
#print axioms Seed.Eighth.proj_identify
#print axioms Seed.Eighth.proj_ofR_false
#print axioms Seed.Eighth.proj_ofR_true
#print axioms Seed.Eighth.ofR_nothing_in_s
#print axioms Seed.Eighth.ofR_wf
#print axioms Seed.Eighth.ofR_addTerm
#print axioms Seed.Eighth.ofR_addAssertion
#print axioms Seed.Eighth.ofR_remove
#print axioms Seed.Eighth.identify_zero
#print axioms Seed.Eighth.ofR_identify
#print axioms Seed.Eighth.eq_ofR_of_nothing_in_s
#print axioms Seed.Eighth.size_eq
#print axioms Seed.Eighth.size_ofR
#print axioms Seed.Eighth.wf_proj
#print axioms Seed.Eighth.givenA8_wf
#print axioms Seed.Eighth.givenA8_a
#print axioms Seed.Eighth.givenA8_b
#print axioms Seed.Eighth.givenB8_a
#print axioms Seed.Eighth.givenB8_b
#print axioms Seed.Eighth.givenA8_proj
#print axioms Seed.Eighth.not_ne
#print axioms Seed.Eighth.givenB8_wf
#print axioms Seed.Eighth.size_givenA8
#print axioms Seed.Eighth.size_givenB8

-- Eighth/Step: the four kinds over two relations, the embedding, the projections, invariants
#print axioms Seed.Sixth.Step6.ofR
#print axioms Seed.Eighth.Step8.proj
#print axioms Seed.Eighth.Step8.proj_self
#print axioms Seed.Eighth.Step8.wf
#print axioms Seed.Eighth.Step8.nonempty
#print axioms Seed.Eighth.Step8.names_stay_merged
#print axioms Seed.Eighth.Reach8.trans
#print axioms Seed.Eighth.Reach8.eq_of_zero
#print axioms Seed.Eighth.Reach8.wf
#print axioms Seed.Eighth.Reach8.nonempty
#print axioms Seed.Eighth.Reach8.names_stay_merged
#print axioms Seed.Sixth.Reach6.ofR
#print axioms Seed.Eighth.Reach8.proj

-- Eighth/Cost: the potential per relation, the bounds, additivity, parity
#print axioms Seed.Eighth.costA8_eq
#print axioms Seed.Eighth.costB8_eq
#print axioms Seed.Eighth.costA8_ofR
#print axioms Seed.Eighth.costB8_ofR
#print axioms Seed.Eighth.Step8.size_step
#print axioms Seed.Eighth.Reach8.size_parity
#print axioms Seed.Eighth.Step8.split
#print axioms Seed.Eighth.Step8.costA_le
#print axioms Seed.Eighth.Step8.costB_le
#print axioms Seed.Eighth.Reach8.costA_le
#print axioms Seed.Eighth.Reach8.costB_le
#print axioms Seed.Eighth.costA8_givenA8
#print axioms Seed.Eighth.costB8_givenB8
#print axioms Seed.Eighth.fewest_changes8_lower_A
#print axioms Seed.Eighth.fewest_changes8_lower_B
#print axioms Seed.Eighth.reach8_raise
#print axioms Seed.Eighth.reach8_from_ofR
#print axioms Seed.Eighth.fewest_changes8_A
#print axioms Seed.Eighth.fewest_changes8_B
#print axioms Seed.Eighth.fewest_changes8_of_r_A
#print axioms Seed.Eighth.fewest_changes8_of_r_B
#print axioms Seed.Eighth.s_costs_its_total

-- Eighth/Reach: clearing `s`, the criterion, the results, mutual reachability, cycles
#print axioms Seed.Eighth.reach8_clear_s
#print axioms Seed.Eighth.reach8_of_names
#print axioms Seed.Eighth.reach8_iff
#print axioms Seed.Eighth.reach8_iff_r
#print axioms Seed.Eighth.result8_iff_A
#print axioms Seed.Eighth.result8_iff_B
#print axioms Seed.Eighth.results_pair
#print axioms Seed.Eighth.s_is_a_result
#print axioms Seed.Eighth.reach8_symm
#print axioms Seed.Eighth.reach8_back_A
#print axioms Seed.Eighth.reach8_total
#print axioms Seed.Eighth.merged_never_apart8
#print axioms Seed.Eighth.remove_addAssertion
#print axioms Seed.Eighth.cycle2_8
#print axioms Seed.Eighth.Reach8.cycles
#print axioms Seed.Eighth.Reach8.unbounded
#print axioms Seed.Eighth.no_return_fails8
#print axioms Seed.Eighth.antisymm_fails8
#print axioms Seed.Eighth.length_not_unique8

-- Eighth/Compare: what survives the second relation
#print axioms Seed.Eighth.results_ofR_A
#print axioms Seed.Eighth.results_ofR_B
#print axioms Seed.Eighth.results_r_iff
#print axioms Seed.Eighth.results_grow
#print axioms Seed.Eighth.proj_results
#print axioms Seed.Eighth.criterion_survives
#print axioms Seed.Eighth.cost_survives
#print axioms Seed.Eighth.same_r_part_mutual
#print axioms Seed.Eighth.interaction

-- Eighth/Rename: rewriting both relations
#print axioms Seed.Eighth.proj_rename8
#print axioms Seed.Eighth.rename8_addTerm
#print axioms Seed.Eighth.rename8_addAssertion
#print axioms Seed.Eighth.rename8_remove
#print axioms Seed.Eighth.rename8_identify
#print axioms Seed.Eighth.wf_rename8
#print axioms Seed.Eighth.size_rename8
#print axioms Seed.Eighth.Step8.rename
#print axioms Seed.Eighth.Reach8.rename
#print axioms Seed.Eighth.costA8_rename
#print axioms Seed.Eighth.costB8_rename
#print axioms Seed.Eighth.rename8_ofR
#print axioms Seed.Eighth.fewest_changes8_every_writing_A
#print axioms Seed.Eighth.fewest_changes8_every_writing_B

-- Earlier derivations, cited and re-checked by the eighth paper
#print axioms Seed.bra_not_derived
#print axioms Seed.bra_not_refuted
#print axioms Seed.Fifth.contains_fails
#print axioms Seed.Fifth.reach5_clear
#print axioms Seed.Fourth.total_addTerm
#print axioms Seed.Fourth.total_addAssertion
#print axioms Seed.Fourth.size_addTerm
#print axioms Seed.Fourth.rename4_addTerm
#print axioms Seed.Fourth.rename4_addAssertion
#print axioms Seed.Fourth.total_rename4
#print axioms Seed.Fourth.wf_rename4
#print axioms Seed.Fifth.total_remove
#print axioms Seed.Fifth.total_identify
#print axioms Seed.Fifth.size_identify
#print axioms Seed.Fifth.rename4_remove
#print axioms Seed.Fifth.rename4_identify
#print axioms Seed.Fifth.exists_writing5
#print axioms Seed.Fifth.antisymm_fails
#print axioms Seed.Sixth.Step6.wf
#print axioms Seed.Sixth.Step6.nonempty
#print axioms Seed.Sixth.Step6.names_stay_merged
#print axioms Seed.Sixth.Step6.costA_le
#print axioms Seed.Sixth.Step6.costB_le
#print axioms Seed.Sixth.reach6_of_names
#print axioms Seed.Sixth.reach6_iff
#print axioms Seed.Sixth.result6_iff_A
#print axioms Seed.Sixth.fewest_changes6_A
#print axioms Seed.Sixth.fewest_changes6_B
#print axioms Seed.Sixth.costA6_givenA4
#print axioms Seed.Sixth.costB6_givenB4
#print axioms Seed.Sixth.costA6_rename
#print axioms Seed.Sixth.costB6_rename
#print axioms Seed.Sixth.no_return_fails6

-- Whole-repo review: cited sixth-derivation upper-bound construction.
#print axioms Seed.Sixth.reach6_raise
