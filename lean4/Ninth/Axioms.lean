import Ninth.Rename

/-!
# What every theorem cited by the ninth paper rests on

`python code/lean_report_ninth.py` runs this file and stores the output in
`evidence/ninth/lean_axioms.txt`.  Every theorem cited in `paper/ninth/` is
listed: those of the ninth library (`Seed.Ninth`), and those of the earlier
derivations that the ninth paper cites and re-checks.  Names are written in
full, since the libraries re-prove some theorems under similar short names.
-/

-- Ninth/State: two relations without names, the maps, the empty state, the exchange
#print axioms Seed.Ninth.ext_proj9
#print axioms Seed.Ninth.proj9_addTerm
#print axioms Seed.Ninth.proj9_addAssertion_self
#print axioms Seed.Ninth.proj9_addAssertion_other
#print axioms Seed.Ninth.proj9_remove_self
#print axioms Seed.Ninth.proj9_remove_other
#print axioms Seed.Ninth.proj9_identify
#print axioms Seed.Ninth.wf_proj9
#print axioms Seed.Ninth.forget_name9
#print axioms Seed.Ninth.name9_names_one_term
#print axioms Seed.Ninth.proj_name9
#print axioms Seed.Ninth.proj_forget9
#print axioms Seed.Ninth.name9_addTerm
#print axioms Seed.Ninth.name9_addAssertion
#print axioms Seed.Ninth.name9_remove
#print axioms Seed.Ninth.name9_identify
#print axioms Seed.Ninth.forget9_addTerm
#print axioms Seed.Ninth.forget9_addAssertion
#print axioms Seed.Ninth.forget9_remove
#print axioms Seed.Ninth.forget9_identify
#print axioms Seed.Ninth.size_name9
#print axioms Seed.Ninth.size_forget9
#print axioms Seed.Ninth.name9_wf
#print axioms Seed.Ninth.wf_of_name9
#print axioms Seed.Ninth.wf_forget9
#print axioms Seed.Ninth.proj_ofR9_false
#print axioms Seed.Ninth.proj_ofR9_true
#print axioms Seed.Ninth.ofR9_nothing_in_s
#print axioms Seed.Ninth.ofR9_wf
#print axioms Seed.Ninth.ofR9_addTerm
#print axioms Seed.Ninth.ofR9_addAssertion
#print axioms Seed.Ninth.ofR9_remove
#print axioms Seed.Ninth.identify_zero9
#print axioms Seed.Ninth.ofR9_identify
#print axioms Seed.Ninth.eq_ofR9_of_nothing_in_s
#print axioms Seed.Ninth.ofR9_empty
#print axioms Seed.Ninth.swap9_swap
#print axioms Seed.Ninth.proj9_swap
#print axioms Seed.Ninth.swap9_wf
#print axioms Seed.Ninth.swap9_empty
#print axioms Seed.Ninth.empty9_wf
#print axioms Seed.Ninth.empty9_size
#print axioms Seed.Ninth.empty9_not_nonempty
#print axioms Seed.Ninth.eq_empty9_of_wf
#print axioms Seed.Ninth.size9_eq
#print axioms Seed.Ninth.size9_swap
#print axioms Seed.Ninth.size_addTerm9
#print axioms Seed.Ninth.addTerm9_wf
#print axioms Seed.Ninth.size_addAssertion9
#print axioms Seed.Ninth.size_remove9
#print axioms Seed.Ninth.size_identify9
#print axioms Seed.Ninth.size_oneTerm9
#print axioms Seed.Ninth.oneTerm9_wf

-- Ninth/Step: the four kinds over two relations, embeddings, invariants
#print axioms Seed.Eighth.Step8.forget
#print axioms Seed.Ninth.Step9.name
#print axioms Seed.Seventh.Step7.ofR
#print axioms Seed.Ninth.Step9.proj
#print axioms Seed.Ninth.Step9.swap
#print axioms Seed.Ninth.Step9.wf
#print axioms Seed.Ninth.Step9.nonempty_out
#print axioms Seed.Ninth.Step9.nonempty
#print axioms Seed.Ninth.first_change_adds_term9
#print axioms Seed.Ninth.Reach9.trans
#print axioms Seed.Ninth.Reach9.eq_of_zero
#print axioms Seed.Ninth.Reach9.wf
#print axioms Seed.Ninth.Reach9.nonempty
#print axioms Seed.Eighth.Reach8.forget
#print axioms Seed.Ninth.Reach9.name
#print axioms Seed.Seventh.Reach7.ofR
#print axioms Seed.Ninth.Reach9.proj
#print axioms Seed.Ninth.Reach9.swap
#print axioms Seed.Ninth.reach9_empty_iff

-- Ninth/Cost: the size as the cost, additivity per relation, additions only
#print axioms Seed.Ninth.Step9.size_step
#print axioms Seed.Ninth.Reach9.size_le
#print axioms Seed.Ninth.Reach9.size_parity
#print axioms Seed.Ninth.fewest_changes9_lower
#print axioms Seed.Ninth.reach9_addTerms
#print axioms Seed.Ninth.reach9_raise
#print axioms Seed.Ninth.reach9_by_additions
#print axioms Seed.Ninth.fewest_changes9
#print axioms Seed.Ninth.cost_oneTerm9
#print axioms Seed.Ninth.cost_adds_up9
#print axioms Seed.Ninth.cost_adds_up9_swapped
#print axioms Seed.Ninth.cost_not_sum_of_parts9
#print axioms Seed.Ninth.one_term_parts9
#print axioms Seed.Ninth.Step9.lowers_or_adds
#print axioms Seed.Ninth.shortest_are_additions9

-- Ninth/Reach: has a term, jointly free, one-way out of empty, the exchange
#print axioms Seed.Ninth.reach9_of_nonempty
#print axioms Seed.Ninth.reach9_iff
#print axioms Seed.Ninth.result9_iff
#print axioms Seed.Ninth.empty9_is_a_result
#print axioms Seed.Ninth.results_pair9
#print axioms Seed.Ninth.reach9_symm
#print axioms Seed.Ninth.reach9_total
#print axioms Seed.Ninth.empty9_never_returned
#print axioms Seed.Ninth.no_cycle_at_empty9
#print axioms Seed.Ninth.reach9_swap
#print axioms Seed.Ninth.result9_swap
#print axioms Seed.Ninth.cycle2_9
#print axioms Seed.Ninth.Reach9.cycles
#print axioms Seed.Ninth.Reach9.unbounded
#print axioms Seed.Ninth.no_return_fails9
#print axioms Seed.Ninth.antisymm_fails9
#print axioms Seed.Ninth.length_not_unique9

-- Ninth/Compare: what survives with nothing given and two relations
#print axioms Seed.Ninth.results_ofR7
#print axioms Seed.Ninth.results_r_iff9
#print axioms Seed.Ninth.results_s_iff9
#print axioms Seed.Ninth.proj_results9
#print axioms Seed.Ninth.cost_survives7
#print axioms Seed.Ninth.criterion_survives7
#print axioms Seed.Ninth.results_forget8_A
#print axioms Seed.Ninth.results_forget8_B
#print axioms Seed.Ninth.results_name8
#print axioms Seed.Ninth.eighth_never_empty
#print axioms Seed.Ninth.empty9_is_new
#print axioms Seed.Ninth.criterion_survives8
#print axioms Seed.Ninth.costA8_oneTerm9
#print axioms Seed.Ninth.eighth_cost_fails
#print axioms Seed.Ninth.size_difference_survives9
#print axioms Seed.Ninth.names_merged_vacuous9
#print axioms Seed.Ninth.interaction9
#print axioms Seed.Ninth.exchange_symmetry9

-- Ninth/Rename: rewriting both relations, one sameness
#print axioms Seed.Ninth.rename8_name
#print axioms Seed.Ninth.forget_rename8
#print axioms Seed.Ninth.proj_rename9
#print axioms Seed.Ninth.rename9_addTerm
#print axioms Seed.Ninth.rename9_addAssertion
#print axioms Seed.Ninth.rename9_remove
#print axioms Seed.Ninth.rename9_identify
#print axioms Seed.Ninth.size_rename9
#print axioms Seed.Ninth.wf_rename9
#print axioms Seed.Ninth.rename9_empty
#print axioms Seed.Ninth.Step9.rename
#print axioms Seed.Ninth.Reach9.rename
#print axioms Seed.Ninth.fewest_changes9_every_writing
#print axioms Seed.Ninth.rename9_swap

-- Earlier derivations, cited and re-checked by the ninth paper
#print axioms Seed.Seventh.fewest_changes7
#print axioms Seed.Seventh.reach7_iff
#print axioms Seed.Seventh.result7_iff
#print axioms Seed.Seventh.empty_is_a_result
#print axioms Seed.Seventh.empty_never_returned
#print axioms Seed.Seventh.first_change_adds_term
#print axioms Seed.Seventh.shortest_are_additions
#print axioms Seed.Eighth.fewest_changes8_A
#print axioms Seed.Eighth.reach8_iff
#print axioms Seed.Eighth.result8_iff_A
#print axioms Seed.Eighth.results_pair
#print axioms Seed.Eighth.results_r_iff
#print axioms Seed.Eighth.cost_survives
#print axioms Seed.Eighth.criterion_survives
#print axioms Seed.Eighth.s_costs_its_total

-- Whole-repo review: cited eighth-derivation invariants and paths.
#print axioms Seed.Eighth.Reach8.nonempty
#print axioms Seed.Eighth.Step8.size_step
#print axioms Seed.Eighth.cycle2_8
#print axioms Seed.Eighth.fewest_changes8_lower_A
#print axioms Seed.Eighth.reach8_of_names
#print axioms Seed.Eighth.reach8_raise
#print axioms Seed.Eighth.rename8_addTerm
#print axioms Seed.Fifth.contains_fails
