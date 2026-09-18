import H3V7N5QF.Answers

/-!
# What every cited theorem rests on

`python code/lean_report.py` runs this file and stores the output in
`evidence/lean_axioms.txt`.  Every theorem cited in `paper/` is listed.
-/

open Seed

-- Basic: what is given
#print axioms given_distinct
#print axioms bra_not_refuted
#print axioms bra_not_derived
#print axioms two_states_on_given_terms
#print axioms two_states_differ
#print axioms passing_on_refutes_bra
#print axioms image_loop_iff
#print axioms identification_obstructed_iff
#print axioms loop_survives_replacement
#print axioms loop_survives_additions
#print axioms only_removal_restores

-- Finite: changes, obstruction, invariants
#print axioms identify_legal_iff
#print axioms addAssertion_legal_iff
#print axioms adding_xrx_always_obstructed
#print axioms remove_legal
#print axioms addTerm_legal
#print axioms Step.legal
#print axioms Step.wf
#print axioms Step.nonempty
#print axioms Step.names_stay_merged
#print axioms obstruction_persists
#print axioms identify_keeps_apart

-- Cost: the lower bound
#print axioms Step.costA_le
#print axioms Step.costB_le
#print axioms Reach.legal
#print axioms Reach.wf
#print axioms Reach.nonempty
#print axioms Reach.names_stay_merged
#print axioms Reach.arb_gone_for_good
#print axioms fewest_changes_lower_A
#print axioms fewest_changes_lower_B
#print axioms givenA_to_givenB
#print axioms givenB_to_givenA

-- Paths: the upper bound
#print axioms reach_by_edits
#print axioms edits_count
#print axioms givenA_to_oneTerm
#print axioms givenB_to_oneTerm
#print axioms fewest_changes_A
#print axioms fewest_changes_B

-- Answers
#print axioms remove_obstruction_first_or_last
#print axioms remove_answer_one_way
#print axioms remove_answer_two_way
#print axioms build_answer
#print axioms build_answer_reverse
#print axioms build_gives_back
#print axioms build_reverse_gives_back
#print axioms build_needs_term_and_assertion
