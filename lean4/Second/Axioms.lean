import Second.Answers

/-!
# What every theorem cited by the second paper rests on

`python code/lean_report_second.py` runs this file and stores the output in
`evidence/second/lean_axioms.txt`.  Every theorem cited in `paper/second/` is
listed: those of the second library (`Seed.Second`) and those of the first
derivation that the second paper cites and re-checks (`Seed`).
-/

open Seed Seed.Second

-- Second/Step: the three kinds, the embedding, inherited invariants
#print axioms Step3.toStep
#print axioms Step.remove_or_step3
#print axioms Step3.ne_remove
#print axioms Step3.legal
#print axioms Step3.wf
#print axioms Step3.nonempty
#print axioms Reach3.toReach
#print axioms Reach3.legal
#print axioms Reach3.wf
#print axioms Reach3.nonempty
#print axioms Reach3.costA_le_inherited
#print axioms Reach3.costB_le_inherited

-- Second/Carry: the carrying map and its consequences
#print axioms Step3.carries
#print axioms Reach3.carries
#print axioms Reach3.arb_persists
#print axioms Reach3.bra_persists
#print axioms Reach3.names_apart
#print axioms Reach3.two_terms
#print axioms Reach3.obstruction_persists
#print axioms Reach3.identify_images_obstructed
#print axioms Reach3.split_mono

-- Second/Cost: the size difference
#print axioms Step3.size_le
#print axioms Reach3.size_le
#print axioms fewest_changes3_lower_A
#print axioms fewest_changes3_lower_B
#print axioms reach3_by_additions
#print axioms additions_count
#print axioms fewest_changes3_A
#print axioms fewest_changes3_B
#print axioms reach3_givenA_contains
#print axioms reach3_givenB_contains
#print axioms reach3_givenA_two_terms
#print axioms reach3_givenB_two_terms
#print axioms oneTerm_unreachable_A
#print axioms oneTerm_unreachable_B
#print axioms givenA_to_givenB3
#print axioms givenB_never_givenA
#print axioms lostA_eq_zero_of_reach3
#print axioms lostB_eq_zero_of_reach3
#print axioms costA_eq_size_of_reach3
#print axioms costB_eq_size_of_reach3

-- Second/Rename: rewriting
#print axioms Step3.rename
#print axioms Reach3.rename
#print axioms size_rename
#print axioms result_iff_A
#print axioms result_iff_B
#print axioms fewest_changes3_every_writing_A
#print axioms fewest_changes3_every_writing_B

-- Second/Answers
#print axioms build_answer3
#print axioms build_answer3_reverse
#print axioms removal_answer_outcome_unreachable

-- First derivation, cited and re-checked (statements that mention no change)
#print axioms given_distinct
#print axioms bra_not_refuted
#print axioms bra_not_derived
#print axioms two_states_on_given_terms
#print axioms two_states_differ
#print axioms passing_on_refutes_bra
#print axioms identify_legal_iff
#print axioms addAssertion_legal_iff
#print axioms adding_xrx_always_obstructed
#print axioms addTerm_legal
#print axioms identify_keeps_apart
#print axioms only_removal_restores
#print axioms build_gives_back
#print axioms build_reverse_gives_back
#print axioms build_needs_term_and_assertion

-- First derivation, cited and re-checked through the embedding `Step3.toStep`
#print axioms Step.legal
#print axioms Step.wf
#print axioms Step.nonempty
#print axioms obstruction_persists
#print axioms fewest_changes_lower_A
#print axioms fewest_changes_lower_B

-- Whole-repo review: base theorems cited by this paper and ledger.
#print axioms Seed.Reach.legal
#print axioms Seed.Reach.nonempty
#print axioms Seed.Reach.wf
#print axioms Seed.givenA_to_givenB
#print axioms Seed.givenB_to_givenA
#print axioms Seed.reach_by_edits
#print axioms Seed.remove_legal
