import Twentieth.Order

/-!
`python code/lean_report_twentieth.py` stores this output in
`evidence/twentieth/lean_axioms.txt`.
-/

open Seed.Twentieth

#print axioms reach_cleared
#print axioms added_oneTerm
#print axioms added_cleared
#print axioms additions_diverge

-- Base theorems this paper cites in its re-checks.
#print axioms Seed.addTerm_legal
#print axioms Seed.givenA_to_oneTerm
#print axioms Seed.fewest_changes_lower_A
#print axioms Seed.fewest_changes_lower_B
