import Sixth.Rename

/-!
# What every theorem cited by the sixth paper rests on

`python code/lean_report_sixth.py` runs this file and stores the output in
`evidence/sixth/lean_axioms.txt`.  Every theorem cited in `paper/sixth/` is
listed: those of the sixth library (`Seed.Sixth`), and those of the earlier
derivations that the sixth paper cites and re-checks.  Names are written in
full, since the libraries re-prove some theorems under similar short names.
-/

-- Sixth/State: identification with something between or at the merged terms; the one-term states
#print axioms Seed.Sixth.identify_M_ge_pair
#print axioms Seed.Sixth.identify_M_eq_zero_of_all_merged
#print axioms Seed.Sixth.loopState_wf
#print axioms Seed.Sixth.loopState_zero
#print axioms Seed.Sixth.size_loopState
#print axioms Seed.Sixth.loopState_contains

-- Sixth/Step: the four kinds with nothing forbidden, the embeddings, invariants
#print axioms Seed.Fifth.Step5.toStep6
#print axioms Seed.Fifth.Try5.toStep6
#print axioms Seed.Sixth.Step6.toTry5
#print axioms Seed.Sixth.try5_iff_step6
#print axioms Seed.Sixth.Step6.not_legal_iff
#print axioms Seed.Sixth.Step6.toStep5
#print axioms Seed.Sixth.Step6.wf
#print axioms Seed.Sixth.Step6.nonempty
#print axioms Seed.Sixth.Step6.names_stay_merged
#print axioms Seed.Sixth.Reach6.trans
#print axioms Seed.Sixth.Reach6.eq_of_zero
#print axioms Seed.Sixth.Reach6.wf
#print axioms Seed.Sixth.Reach6.nonempty
#print axioms Seed.Fifth.Reach5.toReach6
#print axioms Seed.Sixth.Reach6.names_stay_merged
#print axioms Seed.Sixth.Reach6.toReach5_of_legal_step
#print axioms Seed.Sixth.identify_given_ara
#print axioms Seed.Sixth.legal_not_kept
#print axioms Seed.Sixth.arb_gone_fails

-- Sixth/Cost: the potential, the lower and upper bounds, parity, what survives
#print axioms Seed.Sixth.lostA6_eq_lostA5_of_ne
#print axioms Seed.Sixth.lostB6_eq_lostB5_of_ne
#print axioms Seed.Sixth.lostA6_eq_lostA5_of_legal
#print axioms Seed.Sixth.lostB6_eq_lostB5_of_legal
#print axioms Seed.Sixth.costA6_eq_costA5_of_legal
#print axioms Seed.Sixth.costB6_eq_costB5_of_legal
#print axioms Seed.Sixth.lostA6_le_two
#print axioms Seed.Sixth.lostB6_le_three
#print axioms Seed.Sixth.lostA6_le_of_contains
#print axioms Seed.Sixth.lostB6_le_of_contains
#print axioms Seed.Sixth.addAssertion_contains
#print axioms Seed.Sixth.lostA6_remove
#print axioms Seed.Sixth.lostB6_remove
#print axioms Seed.Sixth.lostA6_identify
#print axioms Seed.Sixth.lostB6_identify
#print axioms Seed.Sixth.Step6.costA_le
#print axioms Seed.Sixth.Step6.costB_le
#print axioms Seed.Sixth.Reach6.costA_le
#print axioms Seed.Sixth.Reach6.costB_le
#print axioms Seed.Sixth.Step6.size_step
#print axioms Seed.Sixth.Reach6.size_parity
#print axioms Seed.Sixth.costA6_givenA4
#print axioms Seed.Sixth.costB6_givenB4
#print axioms Seed.Sixth.fewest_changes6_lower_A
#print axioms Seed.Sixth.fewest_changes6_lower_B
#print axioms Seed.Sixth.reach6_addTerms
#print axioms Seed.Sixth.reach6_raise
#print axioms Seed.Sixth.reach6_by_additions
#print axioms Seed.Sixth.reach6_of_contains
#print axioms Seed.Sixth.fewest_changes6_upper_A_apart
#print axioms Seed.Sixth.identify_givenA4_eq
#print axioms Seed.Sixth.step_identify_givenA4
#print axioms Seed.Sixth.fewest_changes6_upper_A_merged
#print axioms Seed.Sixth.fewest_changes6_A
#print axioms Seed.Sixth.fewest_changes6_upper_B_apart
#print axioms Seed.Sixth.identify_givenB4_eq
#print axioms Seed.Sixth.step_identify_givenB4
#print axioms Seed.Sixth.givenB4_to_loopState_one
#print axioms Seed.Sixth.fewest_changes6_upper_B_merged
#print axioms Seed.Sixth.fewest_changes6_B
#print axioms Seed.Sixth.fewest_changes6_of_legal_A
#print axioms Seed.Sixth.fewest_changes6_of_legal_B
#print axioms Seed.Sixth.fewest_changes6_apart_A
#print axioms Seed.Sixth.lostA6_eq_zero_of_contains
#print axioms Seed.Sixth.lostB6_eq_zero_of_contains
#print axioms Seed.Sixth.fewest_changes6_of_contains_A
#print axioms Seed.Sixth.fewest_changes6_of_contains_B
#print axioms Seed.Sixth.fifth_potential_fails
#print axioms Seed.Sixth.cost_loopState

-- Sixth/Reach: the criterion, the results, mutual reachability, cycles
#print axioms Seed.Sixth.reach6_of_names
#print axioms Seed.Sixth.reach6_iff
#print axioms Seed.Sixth.result6_iff_A
#print axioms Seed.Sixth.result6_iff_B
#print axioms Seed.Sixth.xrx_is_a_result
#print axioms Seed.Sixth.loopState_is_a_result
#print axioms Seed.Sixth.reach6_symm
#print axioms Seed.Sixth.reach6_back_A
#print axioms Seed.Sixth.reach6_back_B
#print axioms Seed.Sixth.reach6_total
#print axioms Seed.Sixth.merged_never_apart6
#print axioms Seed.Sixth.loopState_never_apart
#print axioms Seed.Sixth.cycle2_6
#print axioms Seed.Sixth.Reach6.cycles
#print axioms Seed.Sixth.Reach6.unbounded
#print axioms Seed.Sixth.no_return_fails6
#print axioms Seed.Sixth.antisymm_fails6
#print axioms Seed.Sixth.length_not_unique6
#print axioms Seed.Sixth.contains4_reach6
#print axioms Seed.Sixth.criterion_not_containment

-- Sixth/Compare: what survives once nothing is forbidden
#print axioms Seed.Sixth.results_extend_A
#print axioms Seed.Sixth.results_extend_B
#print axioms Seed.Sixth.results_grow
#print axioms Seed.Sixth.results_are_every_wf_state
#print axioms Seed.Sixth.legal_results_are_the_fifths
#print axioms Seed.Sixth.criterion_survives
#print axioms Seed.Sixth.cost_survives_on_legal
#print axioms Seed.Sixth.cost_survives_names_apart
#print axioms Seed.Sixth.cost_fails_names_merged
#print axioms Seed.Sixth.nothing_obstructed
#print axioms Seed.Sixth.remove_answer_differs
#print axioms Seed.Sixth.first_or_last_fails

-- Sixth/Rename: rewriting the terms
#print axioms Seed.Sixth.Step6.rename
#print axioms Seed.Sixth.Reach6.rename
#print axioms Seed.Sixth.lostA6_rename
#print axioms Seed.Sixth.lostB6_rename
#print axioms Seed.Sixth.costA6_rename
#print axioms Seed.Sixth.costB6_rename
#print axioms Seed.Sixth.fewest_changes6_every_writing_A
#print axioms Seed.Sixth.fewest_changes6_every_writing_B

-- Earlier derivations, cited and re-checked by the sixth paper
#print axioms Seed.given_distinct
#print axioms Seed.bra_not_refuted
#print axioms Seed.bra_not_derived
#print axioms Seed.two_states_on_given_terms
#print axioms Seed.passing_on_refutes_bra
#print axioms Seed.merge_eq_merge
#print axioms Seed.Reach.names_stay_merged
#print axioms Seed.Reach.arb_gone_for_good
#print axioms Seed.Fourth.names_apart_of_legal
#print axioms Seed.Fourth.adding_xrx_always_obstructed4
#print axioms Seed.Fourth.size_addTerm
#print axioms Seed.Fourth.size_addAssertion
#print axioms Seed.Fourth.total_widen
#print axioms Seed.Fourth.reach4_of_contains
#print axioms Seed.Fourth.givenA4_contains
#print axioms Seed.Fourth.givenB4_contains
#print axioms Seed.Fourth.Contains4.antisymm
#print axioms Seed.Fourth.rename4_addTerm
#print axioms Seed.Fourth.rename4_addAssertion
#print axioms Seed.Fourth.rename4_symm_apply
#print axioms Seed.Fourth.wf_rename4
#print axioms Seed.Fifth.identify_M_ge
#print axioms Seed.Fifth.identify_M_eq_zero_iff
#print axioms Seed.Fifth.total_identify
#print axioms Seed.Fifth.size_identify
#print axioms Seed.Fifth.size_remove
#print axioms Seed.Fifth.remove_legal
#print axioms Seed.Fifth.identify_legal_iff
#print axioms Seed.Fifth.Try5.obstructed_iff
#print axioms Seed.Fifth.Try5.legal_iff
#print axioms Seed.Fifth.obstruction_persists5
#print axioms Seed.Fifth.remove_answer5
#print axioms Seed.Fifth.remove_obstruction_first_or_last5
#print axioms Seed.Fifth.Step5.costA_le
#print axioms Seed.Fifth.fewest_changes5_A
#print axioms Seed.Fifth.fewest_changes5_B
#print axioms Seed.Fifth.step_remove_arb
#print axioms Seed.Fifth.removed_arb_contains
#print axioms Seed.Fifth.givenA4_to_oneTerm4
#print axioms Seed.Fifth.givenB4_to_oneTerm4
#print axioms Seed.Fifth.givenB4_remove_bra_eq
#print axioms Seed.Fifth.oneTerm4_contains
#print axioms Seed.Fifth.reach5_clear
#print axioms Seed.Fifth.reach5_collapse
#print axioms Seed.Fifth.move_a_pair
#print axioms Seed.Fifth.move_b_pair
#print axioms Seed.Fifth.two_names_to
#print axioms Seed.Fifth.merge_names
#print axioms Seed.Fifth.move_one
#print axioms Seed.Fifth.reach5_iff
#print axioms Seed.Fifth.result5_iff_A
#print axioms Seed.Fifth.cycle2
#print axioms Seed.Fifth.no_return_fails
#print axioms Seed.Fifth.antisymm_fails
#print axioms Seed.Fifth.criterion_fails
#print axioms Seed.Fifth.Reach5.size_parity
#print axioms Seed.Fifth.Reach5.arb_gone_for_good
#print axioms Seed.Fifth.rename4_remove
#print axioms Seed.Fifth.rename4_identify
#print axioms Seed.Fifth.exists_writing5
#print axioms Seed.Fifth.build_answer5

-- Whole-repo review: cited containment and identification witnesses.
#print axioms Seed.Fifth.contains_fails
#print axioms Seed.Sixth.step_identify_given
