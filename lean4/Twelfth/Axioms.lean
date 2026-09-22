import Twelfth.Rename

/-!
# What every theorem cited by the twelfth paper rests on

`python code/lean_report_twelfth.py` runs this file and stores the output in
`evidence/twelfth/lean_axioms.txt`.
-/

#print axioms Seed.Twelfth.record_determined_by_rel
#print axioms Seed.Twelfth.r_record_not_s
#print axioms Seed.Twelfth.record_not_assertion
#print axioms Seed.Twelfth.identify_drops_a_term
#print axioms Seed.Twelfth.empty_record_restored_by_addTerm
#print axioms Seed.Twelfth.nonempty_not_restored
#print axioms Seed.Twelfth.first_change_adds_term12
#print axioms Seed.Twelfth.fewest_changes12
#print axioms Seed.Twelfth.reach12_iff
#print axioms Seed.Twelfth.results_pair12
#print axioms Seed.Twelfth.no_third_rel
#print axioms Seed.Twelfth.no_cross_constraint
#print axioms Seed.Twelfth.recorded_extra
#print axioms Seed.Twelfth.recorded_cost_is_size
#print axioms Seed.Twelfth.recordRel_swap
#print axioms Seed.Twelfth.recordOf_swap
#print axioms Seed.Twelfth.Step12.swap
#print axioms Seed.Ninth.fewest_changes9
#print axioms Seed.Ninth.reach9_iff
#print axioms Seed.Ninth.results_pair9
