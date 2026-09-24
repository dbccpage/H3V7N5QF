import Fifteenth.Rename

/-!
# What every theorem cited by the fifteenth paper rests on

`python code/lean_report_fifteenth.py` runs this file and stores the output in
`evidence/fifteenth/lean_axioms.txt`.
-/

#print axioms Seed.Fifteenth.reaching_does_not_admit
#print axioms Seed.Fifteenth.admitted_is_admitted
#print axioms Seed.Fifteenth.reaching_ne_admitted
#print axioms Seed.Fifteenth.admission_not_assertion
#print axioms Seed.Fifteenth.admission_not_in_M
#print axioms Seed.Fifteenth.admission_not_a_kind
#print axioms Seed.Fifteenth.first_change_does_not_admit
#print axioms Seed.Fifteenth.r_admission_is_s
#print axioms Seed.Fifteenth.admission_not_of_relation
#print axioms Seed.Fifteenth.fewest_changes15
#print axioms Seed.Fifteenth.reach15_iff
#print axioms Seed.Fifteenth.results_pair15
#print axioms Seed.Fifteenth.no_third_rel
#print axioms Seed.Fifteenth.r_admission_is_s_result
#print axioms Seed.Fifteenth.no_cross_constraint
#print axioms Seed.Fifteenth.every_reached_can_be_admitted
#print axioms Seed.Fifteenth.step_reaches_not_admitted
#print axioms Seed.Fifteenth.tagged_one_nothing
#print axioms Seed.Fifteenth.tagged_cost_fails
#print axioms Seed.Fifteenth.tagged_extra
#print axioms Seed.Fifteenth.admission_swap
#print axioms Seed.Fifteenth.admission_swap_admitted
#print axioms Seed.Fifteenth.Step15.swap
#print axioms Seed.Ninth.fewest_changes9
#print axioms Seed.Ninth.reach9_iff
#print axioms Seed.Ninth.results_pair9

-- Whole-repo review: cited fourteenth-derivation witnesses.
#print axioms Seed.Fourteenth.twoBoth_remove_r
#print axioms Seed.Fourteenth.twoBoth_remove_s
