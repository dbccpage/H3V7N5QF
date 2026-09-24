import Sixteenth.Compare

/-!
# What every theorem cited by the sixteenth paper rests on

`python code/lean_report_sixteenth.py` runs this file and stores the output in
`evidence/sixteenth/lean_axioms.txt`.
-/

#print axioms Seed.Sixteenth.remove_admit_same
#print axioms Seed.Sixteenth.remove_admit_other_ne
#print axioms Seed.Sixteenth.remove_admit_other_ne_direct
#print axioms Seed.Sixteenth.remove_admit_other_st
#print axioms Seed.Sixteenth.add_remove_ne
#print axioms Seed.Sixteenth.add_remove_st
#print axioms Seed.Sixteenth.record_not_raised_by_addition
#print axioms Seed.Sixteenth.potential_addTerm
#print axioms Seed.Sixteenth.potential_addAssertion
#print axioms Seed.Sixteenth.potential_remove
#print axioms Seed.Sixteenth.potential_admit
#print axioms Seed.Sixteenth.potential_identify
#print axioms Seed.Sixteenth.mass_addTerm
#print axioms Seed.Sixteenth.mass_addAssertion
#print axioms Seed.Sixteenth.mass_remove
#print axioms Seed.Sixteenth.mass_admit
#print axioms Seed.Sixteenth.mass_identify
#print axioms Seed.Seventh.NSt.identify_addTerm
#print axioms Seed.Sixteenth.identify_addTerm9
#print axioms Seed.Sixteenth.identify_addTerm16
#print axioms Seed.Sixteenth.potential_swap
#print axioms Seed.Sixteenth.Step16.proj
#print axioms Seed.Ninth.Add9.embed
#print axioms Seed.Ninth.AddReach9.embed
#print axioms Seed.Ninth.Step9.embed
#print axioms Seed.Sixteenth.Step9.embed_identify
#print axioms Seed.Sixteenth.Step16.wf
#print axioms Seed.Sixteenth.Step16.nonempty_out
#print axioms Seed.Sixteenth.Step16.nonempty
#print axioms Seed.Sixteenth.first_change_adds_term16
#print axioms Seed.Sixteenth.Step16.swap
#print axioms Seed.Sixteenth.Reach16.proj
#print axioms Seed.Sixteenth.Reach16.nonempty
#print axioms Seed.Sixteenth.reach16_empty_iff
#print axioms Seed.Sixteenth.Step16.potential_step
#print axioms Seed.Sixteenth.Reach16.potential_le
#print axioms Seed.Sixteenth.Reach16.potential_parity
#print axioms Seed.Sixteenth.fewest_changes16_lower
#print axioms Seed.Sixteenth.Step16.rise_or_fall
#print axioms Seed.Sixteenth.ReachD.potential
#print axioms Seed.Sixteenth.Reach16.toReachD
#print axioms Seed.Sixteenth.no_fall_on_shortest16
#print axioms Seed.Sixteenth.reach16_record
#print axioms Seed.Sixteenth.reach16_by_additions
#print axioms Seed.Sixteenth.fewest_changes16
#print axioms Seed.Sixteenth.fewest_changes16_of_empty_record
#print axioms Seed.Sixteenth.ninth_cost_fails_off_empty_record
#print axioms Seed.Sixteenth.admission_costs_three
#print axioms Seed.Sixteenth.Step16.mass_le
#print axioms Seed.Sixteenth.Reach16.mass_le
#print axioms Seed.Sixteenth.has_term_criterion_fails16
#print axioms Seed.Sixteenth.one_way16
#print axioms Seed.Sixteenth.result16_iff
#print axioms Seed.Sixteenth.results_ninth_iff16
#print axioms Seed.Sixteenth.results_pair16
#print axioms Seed.Sixteenth.cycle2_assert16
#print axioms Seed.Sixteenth.cycle2_16
#print axioms Seed.Sixteenth.Reach16.unbounded
#print axioms Seed.Sixteenth.admit_remove_unbounded
#print axioms Seed.Sixteenth.reach16_admit_all
#print axioms Seed.Sixteenth.reach16_swap
#print axioms Seed.Sixteenth.result16_swap
#print axioms Seed.Sixteenth.ninth_round_survives
#print axioms Seed.Sixteenth.leftOne_is_new
#print axioms Seed.Sixteenth.exchange_symmetry16
#print axioms Seed.Sixteenth.record_names_no_relation
#print axioms Seed.Sixteenth.r_leftover_admitted_into_s
#print axioms Seed.Sixteenth.clearing_is_a_kind16
#print axioms Seed.Sixteenth.admitted_leftover_is_the_assertion
#print axioms Seed.Sixteenth.record_moved_only_by_removal_and_admission
#print axioms Seed.Ninth.fewest_changes9
#print axioms Seed.Ninth.reach9_iff
#print axioms Seed.Ninth.results_pair9
#print axioms Seed.Fourteenth.leftover_remove_r_s
#print axioms Seed.Fourteenth.clearing_not_a_kind
#print axioms Seed.Fourteenth.add_remove

-- Whole-repo review: cited own results absent from the prior report.
#print axioms Seed.Sixteenth.Reach16.swap
#print axioms Seed.Sixteenth.remove_add9
