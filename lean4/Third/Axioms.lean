import Third.Answers

/-!
# What every theorem cited by the third paper rests on

`python code/lean_report_third.py` runs this file and stores the output in
`evidence/third/lean_axioms.txt`.  Every theorem cited in `paper/third/` is
listed: those of the third library (`Seed.Third`), and those of the first and
second derivations that the third paper cites and re-checks (`Seed`,
`Seed.Second`).
-/

open Seed Seed.Second Seed.Third

-- Third/Step: the two kinds, the embeddings, inherited invariants
#print axioms Step2.toStep3
#print axioms Step2.toStep
#print axioms Step3.identify_or_step2
#print axioms Step2.ne_identify
#print axioms Step2.ne_remove
#print axioms Step2.legal
#print axioms Step2.wf
#print axioms Step2.nonempty
#print axioms Reach2.toReach3
#print axioms Reach2.toReach
#print axioms Reach2.trans
#print axioms Reach2.eq_of_zero
#print axioms Reach2.legal
#print axioms Reach2.wf
#print axioms Reach2.nonempty
#print axioms Reach2.size_le_inherited
#print axioms Reach2.costA_le_inherited
#print axioms Reach2.costB_le_inherited

-- Third/Contain: containment and its consequences
#print axioms Contains.antisymm
#print axioms Step2.contains
#print axioms Reach2.contains
#print axioms Contains.carries
#print axioms Reach2.term_persists
#print axioms Reach2.asserted_persists
#print axioms Reach2.name_a
#print axioms Reach2.name_b
#print axioms Reach2.arb_persists
#print axioms Reach2.bra_persists
#print axioms Reach2.names_apart
#print axioms Reach2.two_terms
#print axioms Reach2.card_T_le
#print axioms Reach2.card_A_le
#print axioms Reach2.obstruction_persists
#print axioms Reach2.xrx_still_obstructed
#print axioms Reach2.split_mono

-- Third/Cost: exactly the size difference, one-way reachability
#print axioms Step2.size_eq
#print axioms Reach2.size_eq
#print axioms Reach2.length_unique
#print axioms Reach2.antisymm
#print axioms Reach2.no_return
#print axioms fewest_changes2_lower_A
#print axioms fewest_changes2_lower_B
#print axioms reach2_by_additions
#print axioms reach2_of_contains
#print axioms reach2_iff
#print axioms fewest_changes2_A
#print axioms fewest_changes2_B
#print axioms reach2_givenA_contains
#print axioms reach2_givenB_contains
#print axioms reach2_givenA_two_terms
#print axioms reach2_givenB_two_terms
#print axioms oneTerm_unreachable2_A
#print axioms oneTerm_unreachable2_B
#print axioms givenA_to_givenB2
#print axioms givenB_never_givenA2
#print axioms lostA_eq_zero_of_reach2
#print axioms lostB_eq_zero_of_reach2
#print axioms costA_eq_size_of_reach2
#print axioms costB_eq_size_of_reach2

-- Third/Rename: rewriting
#print axioms Step2.rename
#print axioms Reach2.rename
#print axioms reach2_antisymm_writing
#print axioms result2_iff_A
#print axioms result2_iff_B
#print axioms fewest_changes2_every_writing_A
#print axioms fewest_changes2_every_writing_B
#print axioms reach2_iff_some_writing

-- Third/Answers: attempts, obstructions, answers
#print axioms Step2.toTry2
#print axioms Try2.step2_or_xrx
#print axioms Try2.obstructed_iff
#print axioms Try2.legal_iff
#print axioms addTerm_unobstructed
#print axioms build_answer2
#print axioms build_answer2_reverse
#print axioms no_change_asserts_xrx
#print axioms xrx_outcome_unreachable
#print axioms two_sequences

-- First derivation, cited and re-checked (statements that mention no change)
#print axioms given_distinct
#print axioms bra_not_refuted
#print axioms bra_not_derived
#print axioms two_states_on_given_terms
#print axioms two_states_differ
#print axioms passing_on_refutes_bra
#print axioms addAssertion_legal_iff
#print axioms identify_legal_iff
#print axioms adding_xrx_always_obstructed
#print axioms addTerm_legal
#print axioms build_gives_back
#print axioms build_reverse_gives_back
#print axioms build_needs_term_and_assertion

-- Second derivation, cited and re-checked (statements that mention no change)
#print axioms additions_count
#print axioms size_rename
#print axioms legal_rename
#print axioms wf_rename
#print axioms exists_perm_of_ne
#print axioms rename_symm_apply
#print axioms size_givenA
#print axioms size_givenB
#print axioms givenA_to_givenB3
#print axioms build_answer3

-- Earlier derivations, cited and re-checked through the embeddings
#print axioms Step.legal
#print axioms Step.wf
#print axioms Step.nonempty
#print axioms Step3.toStep
#print axioms Step3.ne_remove
#print axioms Reach3.carries
#print axioms Reach3.arb_persists
#print axioms Reach3.bra_persists
#print axioms Reach3.names_apart
#print axioms Reach3.two_terms
#print axioms Reach3.split_mono
#print axioms Reach3.size_le
#print axioms Reach3.costA_le_inherited
#print axioms Reach3.costB_le_inherited
#print axioms reach3_givenA_contains
#print axioms reach3_givenB_contains
#print axioms oneTerm_unreachable_A
#print axioms oneTerm_unreachable_B
#print axioms givenB_never_givenA
#print axioms lostA_eq_zero_of_reach3
#print axioms lostB_eq_zero_of_reach3
#print axioms costA_eq_size_of_reach3
#print axioms costB_eq_size_of_reach3
#print axioms fewest_changes_lower_A
#print axioms fewest_changes_lower_B

-- Whole-repo review: cited second-derivation step bound.
#print axioms Seed.Second.Step3.size_le
