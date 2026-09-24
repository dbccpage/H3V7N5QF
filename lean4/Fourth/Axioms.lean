import Fourth.Rename

/-!
# What every theorem cited by the fourth paper rests on

`python code/lean_report_fourth.py` runs this file and stores the output in
`evidence/fourth/lean_axioms.txt`.  Every theorem cited in `paper/fourth/` is
listed: those of the fourth library (`Seed.Fourth`), and those of the earlier
derivations that the fourth paper cites and re-checks (`Seed`, `Seed.Second`,
`Seed.Third`).
-/

open Seed Seed.Second Seed.Third Seed.Fourth

-- Fourth/State: the counted state, the two maps, what is given, size
#print axioms toSt_ofSt
#print axioms ofSt_toSt
#print axioms ofSt_simple
#print axioms ofSt_legal
#print axioms ofSt_wf
#print axioms toSt_legal
#print axioms toSt_wf
#print axioms givenA4_legal
#print axioms givenB4_legal
#print axioms givenA4_wf
#print axioms givenB4_wf
#print axioms givenA4_arb
#print axioms givenA4_bra
#print axioms givenB4_arb
#print axioms givenB4_bra
#print axioms toSt_givenA4
#print axioms toSt_givenB4
#print axioms names_apart_of_legal
#print axioms total_addTerm
#print axioms size_addTerm
#print axioms total_addAssertion
#print axioms size_addAssertion
#print axioms size_givenA4
#print axioms size_givenB4
#print axioms size_toSt

-- Fourth/Step: the two kinds, invariants, the embeddings both ways
#print axioms Step4.legal
#print axioms Step4.wf
#print axioms Step4.nonempty
#print axioms Reach4.trans
#print axioms Reach4.eq_of_zero
#print axioms Reach4.legal
#print axioms Reach4.wf
#print axioms Reach4.nonempty
#print axioms ofSt_addTerm
#print axioms ofSt_addAssertion
#print axioms Step2.toStep4
#print axioms Reach2.toReach4
#print axioms toSt_addTerm
#print axioms toSt_addAssertion
#print axioms Step4.mult_zero_of_simple
#print axioms Step4.toStep2
#print axioms Step4.simple_of_simple
#print axioms Reach4.toReach2
#print axioms Reach4.simple_of_simple

-- Fourth/Contain: containment with multiplicities and its consequences
#print axioms Contains4.refl
#print axioms Contains4.trans
#print axioms Contains4.antisymm
#print axioms Step4.contains
#print axioms Reach4.contains
#print axioms Contains4.toSt
#print axioms Contains.ofSt
#print axioms contains4_of_toSt
#print axioms Reach4.term_persists
#print axioms Reach4.mult_le
#print axioms Reach4.asserted_persists
#print axioms Reach4.name_a
#print axioms Reach4.name_b
#print axioms Reach4.arb_persists
#print axioms Reach4.arb_mult_le
#print axioms Reach4.bra_persists
#print axioms Reach4.names_apart
#print axioms Reach4.two_terms
#print axioms Reach4.card_T_le
#print axioms Contains4.total_le
#print axioms Reach4.total_le
#print axioms Reach4.obstruction_persists
#print axioms adding_xrx_always_obstructed4
#print axioms Reach4.xrx_still_obstructed
#print axioms Reach4.split_mono
#print axioms arb_twice

-- Fourth/Cost: exact size, every sequence the same length, reachability is containment
#print axioms Step4.size_eq
#print axioms Reach4.size_eq
#print axioms Reach4.length_unique
#print axioms Reach4.antisymm
#print axioms Reach4.no_return
#print axioms fewest_changes4_lower_A
#print axioms fewest_changes4_lower_B
#print axioms reach4_addTerms
#print axioms reach4_raise
#print axioms total_widen
#print axioms reach4_by_additions
#print axioms reach4_of_contains
#print axioms reach4_iff
#print axioms givenA4_contains
#print axioms givenB4_contains
#print axioms fewest_changes4_upper_A
#print axioms fewest_changes4_upper_B
#print axioms fewest_changes4_A
#print axioms fewest_changes4_B
#print axioms reach4_givenA_contains
#print axioms reach4_givenB_contains
#print axioms reach4_givenA_two_terms
#print axioms reach4_givenB_two_terms
#print axioms oneTerm_unreachable4_A
#print axioms oneTerm_unreachable4_B
#print axioms givenA4_to_givenB4
#print axioms givenB4_never_givenA4

-- Fourth/Answers: attempts, obstructions, builds, removal impossible, two sequences
#print axioms Step4.toTry4
#print axioms Try4.step4_or_xrx
#print axioms Try4.obstructed_iff
#print axioms Try4.legal_iff
#print axioms addTerm_unobstructed4
#print axioms addAssertion_again_unobstructed
#print axioms build_answer4
#print axioms build_answer4_reverse
#print axioms no_change_asserts_xrx4
#print axioms xrx_outcome_unreachable4
#print axioms two_sequences4
#print axioms two_sequences_counted

-- Fourth/Compare: what survives the counting
#print axioms reach4_iff_reach2
#print axioms reach4_givenA_iff
#print axioms reach4_givenB_iff
#print axioms contains4_iff_contains
#print axioms results_extend
#print axioms results_extend_B
#print axioms arb_twice_result
#print axioms size_ofSt
#print axioms antisymm_survives

-- Fourth/Rename: rewriting the terms
#print axioms rename4_addTerm
#print axioms rename4_addAssertion
#print axioms total_rename4
#print axioms size_rename4
#print axioms legal_rename4
#print axioms wf_rename4
#print axioms simple_rename4
#print axioms rename4_symm_apply
#print axioms Step4.rename
#print axioms Reach4.rename
#print axioms reach4_antisymm_writing
#print axioms exists_writing
#print axioms result4_iff_A
#print axioms result4_iff_B
#print axioms fewest_changes4_every_writing_A
#print axioms fewest_changes4_every_writing_B
#print axioms reach4_iff_some_writing

-- Earlier derivations, cited and re-checked by the fourth paper
#print axioms given_distinct
#print axioms bra_not_refuted
#print axioms bra_not_derived
#print axioms two_states_on_given_terms
#print axioms two_states_differ
#print axioms passing_on_refutes_bra
#print axioms given_terms_subset
#print axioms exists_perm_of_ne
#print axioms Carries.split
#print axioms Contains.carries
#print axioms Reach2.antisymm
#print axioms reach2_iff
#print axioms reach2_iff_some_writing
#print axioms fewest_changes2_A
#print axioms fewest_changes2_B
#print axioms result2_iff_A
#print axioms result2_iff_B
#print axioms Reach2.length_unique
#print axioms two_sequences
#print axioms build_gives_back
#print axioms build_needs_term_and_assertion

-- Whole-repo review: cited second- and third-derivation results.
#print axioms Seed.Third.Step2.size_eq
#print axioms Seed.Second.additions_count
#print axioms Seed.Third.givenA_to_givenB2
#print axioms Seed.Second.givenB_never_givenA
