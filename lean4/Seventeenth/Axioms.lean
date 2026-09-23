import Seventeenth.Answers
import Seventeenth.Embed
import Seventeenth.Rename

/-!
# What every cited theorem of the seventeenth derivation rests on

`python code/lean_report_seventeenth.py` runs this file and stores the output
in `evidence/seventeenth/lean_axioms.txt`.
-/

open Seed.Seventeenth

#print axioms hasXrx_iff_not_legal
#print axioms loopyWitness_hasXrx
#print axioms adding_xrx_obstructed
#print axioms adding_xrx_step_obstructed
#print axioms m1_iff_m2_of_loopFree
#print axioms Step17.loopFree_out
#print axioms Step17.no_xrx_of_unobstructed
#print axioms Step17.wf
#print axioms Step17.nonempty
#print axioms Step17.names_stay_merged
#print axioms loopy_m1_allows
#print axioms loopy_m2_obstructs
#print axioms Reach17.loopFree
#print axioms Reach17.wf
#print axioms Reach17.nonempty
#print axioms Reach17.names_stay_merged
#print axioms ReachAll.wf
#print axioms ReachAll.nonempty
#print axioms ReachAll.names_stay_merged
#print axioms Step.toStep17
#print axioms Step.unobstructed17
#print axioms Step17.toStep
#print axioms Reach.toReach17
#print axioms Reach17.toReach
#print axioms fewest_changes17_lower_A
#print axioms fewest_changes17_lower_B
#print axioms fewest_changes17_A
#print axioms fewest_changes17_B
#print axioms identify_givenA_step
#print axioms identify_givenA_reach
#print axioms oneLoop_hasXrx
#print axioms mergedA_hasXrx
#print axioms names_merged_with_loop
#print axioms cost_not_lower_bound_A
#print axioms cost_not_lower_bound_B
#print axioms arb_not_gone
#print axioms add_ara_reach
#print axioms add_ara_hasXrx
#print axioms add_ara_not_unobstructed
#print axioms remove_first_eq_perform_first
#print axioms perform_first_givenA
#print axioms perform_first_intermediate_has_xrx
#print axioms refusal_does_not_enter
#print axioms Step17.rename
#print axioms Reach17.rename
#print axioms ReachAll.rename
#print axioms loopFree_rename

-- Whole-repo review: cited base theorems, in addition to the own theorems above.
#print axioms Seed.Reach.arb_gone_for_good
#print axioms Seed.Reach.legal
#print axioms Seed.Step.legal
#print axioms Seed.adding_xrx_always_obstructed
#print axioms Seed.bra_not_derived
#print axioms Seed.bra_not_refuted
#print axioms Seed.fewest_changes_A
#print axioms Seed.fewest_changes_B
#print axioms Seed.given_distinct
#print axioms Seed.identify_legal_iff
#print axioms Seed.remove_obstruction_first_or_last
#print axioms Seed.two_states_on_given_terms
