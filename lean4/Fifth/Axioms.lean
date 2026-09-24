import Fifth.Rename

/-!
# What every theorem cited by the fifth paper rests on

`python code/lean_report_fifth.py` runs this file and stores the output in
`evidence/fifth/lean_axioms.txt`.  Every theorem cited in `paper/fifth/` is
listed: those of the fifth library (`Seed.Fifth`), and those of the earlier
derivations that the fifth paper cites and re-checks (`Seed`, `Seed.Second`,
`Seed.Third`, `Seed.Fourth`).  Names are written in full, since the fifth
library re-proves some first-derivation theorems under the same short name.
-/

-- Fifth/State: removal and identification on counted states
#print axioms Seed.Fifth.remove_M_self
#print axioms Seed.Fifth.remove_M_of_ne
#print axioms Seed.Fifth.total_remove
#print axioms Seed.Fifth.size_remove
#print axioms Seed.Fifth.identify_M_ge
#print axioms Seed.Fifth.identify_M_eq_zero_iff
#print axioms Seed.Fifth.identify_M_ne_zero
#print axioms Seed.Fifth.merge_eq_left_iff
#print axioms Seed.Fifth.total_identify
#print axioms Seed.Fifth.size_identify
#print axioms Seed.Fifth.toSt_remove
#print axioms Seed.Fifth.toSt_identify

-- Fifth/Step: the four kinds, the embeddings, invariants
#print axioms Seed.Fourth.Step4.toStep5
#print axioms Seed.Fifth.Step5.cases4
#print axioms Seed.Fifth.remove_legal
#print axioms Seed.Fifth.identify_legal_iff
#print axioms Seed.Fifth.Step5.legal
#print axioms Seed.Fifth.Step5.wf
#print axioms Seed.Fifth.Step5.nonempty
#print axioms Seed.Fifth.Step5.names_stay_merged
#print axioms Seed.Fifth.Reach5.trans
#print axioms Seed.Fifth.Reach5.eq_of_zero
#print axioms Seed.Fifth.Reach5.legal
#print axioms Seed.Fifth.Reach5.wf
#print axioms Seed.Fifth.Reach5.nonempty
#print axioms Seed.Fourth.Reach4.toReach5
#print axioms Seed.Fifth.Reach5.names_stay_merged
#print axioms Seed.Fifth.Reach5.arb_gone_for_good
#print axioms Seed.Fifth.Step5.toStep

-- Fifth/Cost: the potential, the lower and upper bounds, parity, what survives
#print axioms Seed.Fifth.miss5_le_of_le
#print axioms Seed.Fifth.lostA5_le_two
#print axioms Seed.Fifth.lostB5_le_three
#print axioms Seed.Fifth.lostA5_le_of_contains
#print axioms Seed.Fifth.lostB5_le_of_contains
#print axioms Seed.Fifth.lostA5_remove
#print axioms Seed.Fifth.lostB5_remove
#print axioms Seed.Fifth.lostA5_identify
#print axioms Seed.Fifth.lostB5_identify
#print axioms Seed.Fifth.Step5.costA_le
#print axioms Seed.Fifth.Step5.costB_le
#print axioms Seed.Fifth.Reach5.costA_le
#print axioms Seed.Fifth.Reach5.costB_le
#print axioms Seed.Fifth.Step5.size_step
#print axioms Seed.Fifth.Reach5.size_parity
#print axioms Seed.Fifth.costA5_givenA4
#print axioms Seed.Fifth.costB5_givenB4
#print axioms Seed.Fifth.fewest_changes5_lower_A
#print axioms Seed.Fifth.fewest_changes5_lower_B
#print axioms Seed.Fifth.removed_arb_contains
#print axioms Seed.Fifth.fewest_changes5_upper_A_apart
#print axioms Seed.Fifth.givenA4_to_oneTerm4
#print axioms Seed.Fifth.oneTerm4_contains
#print axioms Seed.Fifth.fewest_changes5_upper_A_merged
#print axioms Seed.Fifth.fewest_changes5_A
#print axioms Seed.Fifth.fewest_changes5_upper_B_apart
#print axioms Seed.Fifth.givenB4_to_oneTerm4
#print axioms Seed.Fifth.fewest_changes5_upper_B_merged
#print axioms Seed.Fifth.fewest_changes5_B
#print axioms Seed.Fifth.lostA5_eq_zero_of_contains
#print axioms Seed.Fifth.lostB5_eq_zero_of_contains
#print axioms Seed.Fifth.fewest_changes5_of_contains_A
#print axioms Seed.Fifth.fewest_changes5_of_contains_B
#print axioms Seed.Fifth.size_can_fall
#print axioms Seed.Fifth.arb_removed
#print axioms Seed.Fifth.contains_fails

-- Fifth/Reach: the criterion, mutual reachability, cycles, what fails
#print axioms Seed.Fifth.reach5_clear
#print axioms Seed.Fifth.reach5_collapse
#print axioms Seed.Fifth.move_a_pair
#print axioms Seed.Fifth.move_b_pair
#print axioms Seed.Fifth.two_names_to
#print axioms Seed.Fifth.merge_names
#print axioms Seed.Fifth.move_one
#print axioms Seed.Fifth.reach5_of_names
#print axioms Seed.Fifth.reach5_iff
#print axioms Seed.Fifth.result5_iff_A
#print axioms Seed.Fifth.result5_iff_B
#print axioms Seed.Fifth.reach5_symm
#print axioms Seed.Fifth.reach5_back_A
#print axioms Seed.Fifth.reach5_back_B
#print axioms Seed.Fifth.reach5_total
#print axioms Seed.Fifth.merged_never_apart
#print axioms Seed.Fifth.add_identify_back
#print axioms Seed.Fifth.cycle2
#print axioms Seed.Fifth.Reach5.cycles
#print axioms Seed.Fifth.Reach5.unbounded
#print axioms Seed.Fifth.givenB4_remove_bra_eq
#print axioms Seed.Fifth.no_return_fails
#print axioms Seed.Fifth.antisymm_fails
#print axioms Seed.Fifth.length_not_unique

-- Fifth/Answers: attempts, obstructions, the answers
#print axioms Seed.Fifth.Step5.toTry5
#print axioms Seed.Fifth.Try5.step5_or_obstructed
#print axioms Seed.Fifth.Try5.obstructed_iff
#print axioms Seed.Fifth.Try5.legal_iff
#print axioms Seed.Fifth.obstruction_persists5
#print axioms Seed.Fifth.reach5_lower
#print axioms Seed.Fifth.remove_answer5
#print axioms Seed.Fifth.remove_obstruction_first_or_last5
#print axioms Seed.Fifth.build_answer5
#print axioms Seed.Fifth.build_answer5_reverse

-- Fifth/Compare: what survives removal and identification
#print axioms Seed.Fifth.results_extend_A
#print axioms Seed.Fifth.results_extend_B
#print axioms Seed.Fifth.results_grow
#print axioms Seed.Fifth.contains4_reach5
#print axioms Seed.Fifth.criterion_fails
#print axioms Seed.Fifth.cost_survives_length_does_not

-- Fifth/Rename: rewriting the terms
#print axioms Seed.Fifth.rename4_remove
#print axioms Seed.Fifth.merge_perm
#print axioms Seed.Fifth.rename4_identify
#print axioms Seed.Fifth.Step5.rename
#print axioms Seed.Fifth.Reach5.rename
#print axioms Seed.Fifth.lostA5_rename
#print axioms Seed.Fifth.lostB5_rename
#print axioms Seed.Fifth.costA5_rename
#print axioms Seed.Fifth.costB5_rename
#print axioms Seed.Fifth.exists_writing5
#print axioms Seed.Fifth.fewest_changes5_every_writing_A
#print axioms Seed.Fifth.fewest_changes5_every_writing_B

-- Earlier derivations, cited and re-checked by the fifth paper
#print axioms Seed.given_distinct
#print axioms Seed.bra_not_refuted
#print axioms Seed.bra_not_derived
#print axioms Seed.two_states_on_given_terms
#print axioms Seed.passing_on_refutes_bra
#print axioms Seed.merge_eq_merge
#print axioms Seed.identify_legal_iff
#print axioms Seed.obstruction_persists
#print axioms Seed.Step.costA_le
#print axioms Seed.reach_by_edits
#print axioms Seed.fewest_changes_lower_A
#print axioms Seed.fewest_changes_A
#print axioms Seed.givenB_to_givenA
#print axioms Seed.givenA_to_oneTerm
#print axioms Seed.givenB_to_oneTerm
#print axioms Seed.remove_answer_one_way
#print axioms Seed.remove_answer_two_way
#print axioms Seed.Reach.names_stay_merged
#print axioms Seed.Reach.arb_gone_for_good
#print axioms Seed.remove_obstruction_first_or_last
#print axioms Seed.build_gives_back
#print axioms Seed.Second.exists_perm_of_ne
#print axioms Seed.Second.Carries.split
#print axioms Seed.Third.Step2.toStep
#print axioms Seed.Fourth.names_apart_of_legal
#print axioms Seed.Fourth.Step4.contains
#print axioms Seed.Fourth.Contains4.antisymm
#print axioms Seed.Fourth.Reach4.antisymm
#print axioms Seed.Fourth.Reach4.length_unique
#print axioms Seed.Fourth.reach4_iff
#print axioms Seed.Fourth.reach4_of_contains
#print axioms Seed.Fourth.reach4_by_additions
#print axioms Seed.Fourth.fewest_changes4_A
#print axioms Seed.Fourth.Try4.obstructed_iff
#print axioms Seed.Fourth.adding_xrx_always_obstructed4
#print axioms Seed.Fourth.addTerm_unobstructed4
#print axioms Seed.Fourth.addAssertion_again_unobstructed
#print axioms Seed.Fourth.two_sequences4
#print axioms Seed.Fourth.build_answer4
#print axioms Seed.Fourth.build_answer4_reverse
#print axioms Seed.Fourth.givenA4_to_givenB4
#print axioms Seed.Fourth.givenB4_never_givenA4
#print axioms Seed.Fourth.Step4.toStep2
#print axioms Seed.Fourth.toSt_ofSt
#print axioms Seed.Fourth.ofSt_toSt
#print axioms Seed.Fourth.size_rename4
#print axioms Seed.Fourth.Step4.rename
#print axioms Seed.Fourth.rename4_symm_apply

-- Whole-repo review: cited base potential bound.
#print axioms Seed.Reach.costA_le
