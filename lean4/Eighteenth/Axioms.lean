import Eighteenth.Writing

/-!
`python code/lean_report_eighteenth.py` stores this output in
`evidence/eighteenth/lean_axioms.txt`.
-/

open Seed.Eighteenth

#print axioms given_ne_bra
#print axioms swapped_ne_given
#print axioms swapped_ne_bra

-- Base theorems this paper cites in its re-checks.
#print axioms Seed.addTerm_legal
#print axioms Seed.fewest_changes_lower_A
#print axioms Seed.fewest_changes_lower_B
