import Seventh.Rename

/-!
# What every theorem cited by the seventh paper rests on

`python code/lean_report_seventh.py` runs this file and stores the output in
`evidence/seventh/lean_axioms.txt`.  Every theorem cited in `paper/seventh/` is
listed: those of the seventh library (`Seed.Seventh`), and those of the earlier
derivations that the seventh paper cites and re-checks.  Names are written in
full, since the libraries re-prove some theorems under similar short names.
-/

-- Seventh/State: the state without names, the two maps, the empty state
#print axioms Seed.Seventh.forget_name
#print axioms Seed.Seventh.name_names_one_term
#print axioms Seed.Seventh.name_addTerm
#print axioms Seed.Seventh.name_addAssertion
#print axioms Seed.Seventh.name_remove
#print axioms Seed.Seventh.name_identify
#print axioms Seed.Seventh.forget_addTerm
#print axioms Seed.Seventh.forget_addAssertion
#print axioms Seed.Seventh.forget_remove
#print axioms Seed.Seventh.forget_identify
#print axioms Seed.Seventh.size_name
#print axioms Seed.Seventh.size_forget
#print axioms Seed.Seventh.name_wf
#print axioms Seed.Seventh.wf_of_name
#print axioms Seed.Seventh.wf_forget
#print axioms Seed.Seventh.empty_wf
#print axioms Seed.Seventh.empty_size
#print axioms Seed.Seventh.empty_not_nonempty
#print axioms Seed.Seventh.eq_empty_of_wf
#print axioms Seed.Seventh.total_addTerm7
#print axioms Seed.Seventh.size_addTerm7
#print axioms Seed.Seventh.addTerm_wf
#print axioms Seed.Seventh.size_oneTerm7

-- Seventh/Step: the four kinds from nothing, the embeddings, invariants
#print axioms Seed.Sixth.Step6.forget
#print axioms Seed.Seventh.Step7.name
#print axioms Seed.Seventh.Step7.wf
#print axioms Seed.Seventh.Step7.nonempty_out
#print axioms Seed.Seventh.Step7.nonempty
#print axioms Seed.Seventh.first_change_adds_term
#print axioms Seed.Seventh.Reach7.trans
#print axioms Seed.Seventh.Reach7.eq_of_zero
#print axioms Seed.Seventh.Reach7.wf
#print axioms Seed.Seventh.Reach7.nonempty
#print axioms Seed.Sixth.Reach6.forget
#print axioms Seed.Seventh.Reach7.name
#print axioms Seed.Seventh.reach7_empty_iff

-- Seventh/Cost: the size as the cost, the lower and upper bounds, parity, additions only
#print axioms Seed.Seventh.Step7.size_step
#print axioms Seed.Seventh.Reach7.size_le
#print axioms Seed.Seventh.Reach7.size_parity
#print axioms Seed.Seventh.fewest_changes7_lower
#print axioms Seed.Seventh.Contains7.name
#print axioms Seed.Seventh.reach7_of_contains
#print axioms Seed.Seventh.step_first_term
#print axioms Seed.Seventh.reach7_by_additions
#print axioms Seed.Seventh.fewest_changes7
#print axioms Seed.Seventh.cost_oneTerm
#print axioms Seed.Seventh.Add7.toStep7
#print axioms Seed.Seventh.AddReach7.toReach7
#print axioms Seed.Seventh.Step7.lowers_or_adds
#print axioms Seed.Seventh.shortest_are_additions

-- Seventh/Reach: a term decides
#print axioms Seed.Seventh.reach7_of_nonempty
#print axioms Seed.Seventh.reach7_iff
#print axioms Seed.Seventh.result7_iff
#print axioms Seed.Seventh.empty_is_a_result
#print axioms Seed.Seventh.reach7_symm
#print axioms Seed.Seventh.reach7_total
#print axioms Seed.Seventh.empty_never_returned
#print axioms Seed.Seventh.no_cycle_at_empty
#print axioms Seed.Seventh.cycle2_7
#print axioms Seed.Seventh.Reach7.cycles
#print axioms Seed.Seventh.Reach7.unbounded
#print axioms Seed.Seventh.oneTerm7_wf
#print axioms Seed.Seventh.identify_twoTerms7
#print axioms Seed.Seventh.no_return_fails7
#print axioms Seed.Seventh.antisymm_fails7
#print axioms Seed.Seventh.length_not_unique7

-- Seventh/Compare: what survives with nothing given
#print axioms Seed.Seventh.results_forget_A
#print axioms Seed.Seventh.results_forget_B
#print axioms Seed.Seventh.results_name
#print axioms Seed.Seventh.sixth_never_empty
#print axioms Seed.Seventh.empty_is_new
#print axioms Seed.Seventh.criterion_survives
#print axioms Seed.Seventh.costA6_oneTerm7
#print axioms Seed.Seventh.sixth_cost_fails
#print axioms Seed.Seventh.size_difference_survives
#print axioms Seed.Seventh.names_merged_vacuous

-- Seventh/Rename: rewriting the terms
#print axioms Seed.Seventh.rename4_name
#print axioms Seed.Seventh.forget_rename4
#print axioms Seed.Seventh.mem_rename7_T
#print axioms Seed.Seventh.rename7_M
#print axioms Seed.Seventh.rename7_addTerm
#print axioms Seed.Seventh.rename7_addAssertion
#print axioms Seed.Seventh.rename7_remove
#print axioms Seed.Seventh.rename7_identify
#print axioms Seed.Seventh.size_rename7
#print axioms Seed.Seventh.wf_rename7
#print axioms Seed.Seventh.rename7_empty
#print axioms Seed.Seventh.Step7.rename
#print axioms Seed.Seventh.Reach7.rename
#print axioms Seed.Seventh.fewest_changes7_every_writing

-- Earlier derivations, cited and re-checked by the seventh paper
#print axioms Seed.merge_mem_erase
#print axioms Seed.Fourth.size_addAssertion
#print axioms Seed.Fourth.rename4_addTerm
#print axioms Seed.Fourth.rename4_addAssertion
#print axioms Seed.Fourth.mem_rename4_T
#print axioms Seed.Fourth.rename4_M
#print axioms Seed.Fourth.size_rename4
#print axioms Seed.Fifth.size_remove
#print axioms Seed.Fifth.size_identify
#print axioms Seed.Fifth.rename4_remove
#print axioms Seed.Fifth.rename4_identify
#print axioms Seed.Fifth.mem_givenA4_T
#print axioms Seed.Sixth.Step6.wf
#print axioms Seed.Sixth.Step6.size_step
#print axioms Seed.Sixth.Reach6.nonempty
#print axioms Seed.Sixth.Reach6.names_stay_merged
#print axioms Seed.Sixth.reach6_of_contains
#print axioms Seed.Sixth.reach6_of_names
#print axioms Seed.Sixth.reach6_iff
#print axioms Seed.Sixth.result6_iff_A
#print axioms Seed.Sixth.result6_iff_B
#print axioms Seed.Sixth.cycle2_6
#print axioms Seed.Sixth.fewest_changes6_lower_A
#print axioms Seed.Sixth.fewest_changes6_A
#print axioms Seed.Sixth.fewest_changes6_of_contains_A
#print axioms Seed.Sixth.lostA6_of_eq
#print axioms Seed.Sixth.Step6.rename
#print axioms Seed.Sixth.Reach6.rename
