import Tenth.Rename

/-!
# What every theorem cited by the tenth paper rests on

`python code/lean_report_tenth.py` runs this file and stores the output in
`evidence/tenth/lean_axioms.txt`.
-/

#print axioms Seed.Tenth.remove_add_of_pos
#print axioms Seed.Tenth.leftover_addTerm
#print axioms Seed.Tenth.leftover_addAssertion
#print axioms Seed.Tenth.leftover_remove
#print axioms Seed.Tenth.clears_remove
#print axioms Seed.Tenth.leftover_not_assertion
#print axioms Seed.Tenth.first_change_leftover
#print axioms Seed.Tenth.identify_twoEmpty_restored
#print axioms Seed.Tenth.leftover_identify_twoEmpty
#print axioms Seed.Tenth.fewest_changes10
#print axioms Seed.Tenth.reach10_iff
#print axioms Seed.Tenth.results_pair10
#print axioms Seed.Tenth.no_third_rel
#print axioms Seed.Tenth.split_kinds
#print axioms Seed.Tenth.split_additions
#print axioms Seed.Tenth.split_removals
#print axioms Seed.Tenth.other_rel_not_clear
#print axioms Seed.Tenth.tagged_one_nothing
#print axioms Seed.Tenth.tagged_cost_fails
#print axioms Seed.Tenth.tagged_extra
#print axioms Seed.Tenth.leftover_swap_addTerm
#print axioms Seed.Tenth.leftover_swap_remove
#print axioms Seed.Ninth.fewest_changes9
#print axioms Seed.Ninth.reach9_iff
#print axioms Seed.Ninth.results_pair9
#print axioms Seed.Ninth.Step9.swap
