import Nineteenth.Partial

/-!
`python code/lean_report_nineteenth.py` stores this output in
`evidence/nineteenth/lean_axioms.txt`.
-/

open Seed.Nineteenth

#print axioms performPartial_terms
#print axioms cooccur_is_loop
#print axioms side_partial_eq
#print axioms side_partial_legal
#print axioms side_not_identify
#print axioms identify_smaller
#print axioms PStep.card_ge
#print axioms PReach.card_ge
#print axioms oneTerm_unreachable

-- Base theorems this paper cites in its re-checks.
#print axioms Seed.addTerm_legal
#print axioms Seed.givenA_to_oneTerm
