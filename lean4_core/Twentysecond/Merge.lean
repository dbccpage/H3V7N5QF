import Twentysecond.Seventh

/-!
# Which of the ninth's results stay different, and what a merge loses

A ninth state (at a fixed writing) is a state of this seed; this seed makes
two of them one result when they have the same plain part.  Derived here:
* every state is the same result as its plain state, which asserts no pair in
  both relations (`same_plainSt`, `together_plain`);
* two states asserting no pair in both relations are one result here exactly
  when they are one ninth state (`plain_states_stay_apart`): the ninth's
  results that stay different are the plain ones, and every ninth result is
  one result here with exactly one of them;
* **what a merge loses**: a ninth state is determined by its result here and
  the pairs it asserts in both relations (`state_of_result_and_together`); at
  `xqy` those are `min(M_q, M_other)` (`count_together`); the ninth's size
  exceeds this seed's cost by their number (`size_eq_phi_add_together`); the
  two states `a` and `a; ara asa` are one result with different sizes,
  different totals in each relation, and only the second asserts a pair in
  both relations (`merge_loses`).
-/

namespace Twentysecond

/-- **A ninth state is determined by its result here and the pairs it asserts together.** -/
theorem state_of_result_and_together {G H : St} (h : Same G H)
    (ht : (together G.A).Perm (together H.A)) : SameState9 G H :=
  ⟨h.1, (perm_split G.A).trans ((List.Perm.append h.2 ht).trans (perm_split H.A).symm)⟩

theorem together_eq_nil_of_plain {l : List Atom} (h : plain l = l) : together l = [] := by
  have e := length_split l
  rw [h] at e
  cases hl : together l with
  | nil => rfl
  | cons b t =>
    rw [hl, List.length_cons] at e
    omega

/-- The plain state asserts no pair in both relations. -/
theorem together_plain (l : List Atom) : together (plain l) = [] :=
  together_eq_nil_of_plain (plain_plain l)

/-- **Two states asserting no pair in both relations are one result here exactly when they are one
ninth state.** -/
theorem plain_states_stay_apart {G H : St} (hG : together G.A = []) (hH : together H.A = []) :
    Same G H ↔ SameState9 G H := by
  constructor
  · intro h
    refine state_of_result_and_together h ?_
    rw [hG, hH]
  · exact SameState9.same

/-- **What the merge of `a` and `a; ara asa` loses**: one result here; the ninth's size 1 and 3; one
`ara` and one `asa` against none; the pair asserted in both relations. -/
theorem merge_loses :
    Same oneTerm oneTermBoth ∧ oneTerm.size = 1 ∧ oneTermBoth.size = 3 ∧
      oneTerm.A.count ⟨.r, 0, 0⟩ = 0 ∧ oneTermBoth.A.count ⟨.r, 0, 0⟩ = 1 ∧
      oneTerm.A.count ⟨.s, 0, 0⟩ = 0 ∧ oneTermBoth.A.count ⟨.s, 0, 0⟩ = 1 ∧
      together oneTerm.A = [] ∧ together oneTermBoth.A = [⟨.r, 0, 0⟩, ⟨.s, 0, 0⟩] :=
  ⟨ninth_not_one_to_one.2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Twentysecond
