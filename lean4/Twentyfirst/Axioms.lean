import Twentyfirst.Refusal

/-!
`python code/lean_report_twentyfirst.py` stores this output in
`evidence/twentyfirst/lean_axioms.txt`.
-/

open Seed.Twentyfirst

#print axioms no_step_to_illegal
#print axioms identify_given_illegal
#print axioms identify_given_refused
#print axioms refusal_continues_by_a_term
#print axioms refusal_continues_by_removal

-- Base theorems this paper cites in its re-checks.
#print axioms Seed.addTerm_legal
#print axioms Seed.identify_legal_iff
#print axioms Seed.fewest_changes_lower_A
#print axioms Seed.fewest_changes_lower_B
