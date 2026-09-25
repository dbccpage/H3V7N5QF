import Twentyfourth.Swap

/-!
# The twenty-third seed mapped in, and the maps back

Derived here:
* **the twenty-third maps in one to one** (`same24_ofSt_iff`, `Same.lean`),
  each of its changes carried to a change of the same kind
  (`Step.toStep24`, `Basic.lean`); so no two of its results are made one here
  and the merge loses nothing (`no_merge`); the twenty-third's own witnesses
  that the seventh does not map one to one carry over (`seventh_pair_merge24`);
* **the map back** (`readBack`): a result with no filled term to its
  twenty-third result, "none" otherwise.  It returns the original on every
  mapped result (`readBack_ofSt`), answers "none" exactly with a filled term
  (`readBack_none_iff`), and does not depend on the state of the result taken
  (`readBack_congr`); every result it answers "none" on costs at least two
  (`readBack_none_cost`), and **the only one at cost two is one term, filled,
  nothing asserted** (`smallest_none`, `smallest_none_unique`);
* **the forgetting map** (a result to the twenty-third result of its states):
  it answers every result and carries each change to a change or to none
  (`Step24.forget`, `Basic.lean`); it merges results that differ only in their
  filled terms, losing them and the record of which balance
  (`forget_merges`).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- **The twenty-third's witness that the seventh's states do not map one to one merges here too.** -/
theorem seventh_pair_merge24 : Same24 (ofSt (ofR arbTwice)) (ofSt (ofR arbBra)) :=
  same24_ofSt_iff.2 seventh_pair_merge

/-- Is some term filled?  (A decision, by listing the terms.) -/
def anyFilled (X : FSt) : Bool := (List.range X.G.n).any X.F

theorem anyFilled_iff {X : FSt} : anyFilled X = true ↔ X.HasFilled := by
  unfold anyFilled FSt.HasFilled
  simp only [List.any_eq_true, List.mem_range]

/-- The map back: a result with no filled term to its twenty-third result, "none" otherwise. -/
def readBack (X : FSt) : Option St := if anyFilled X = true then none else some X.G

theorem anyFilled_ofSt (G : St) : anyFilled (ofSt G) = false := by
  cases h : anyFilled (ofSt G) with
  | false => rfl
  | true =>
    obtain ⟨_, _, e⟩ := anyFilled_iff.1 h
    exact Bool.noConfusion e

/-- **The map back returns the original on every mapped result.** -/
theorem readBack_ofSt (G : St) : readBack (ofSt G) = some G := by
  unfold readBack
  rw [anyFilled_ofSt]
  rfl

/-- **It answers "none" exactly on the results with a filled term.** -/
theorem readBack_none_iff {X : FSt} : readBack X = none ↔ X.HasFilled := by
  unfold readBack
  cases h : anyFilled X with
  | false =>
    simp only [Bool.false_eq_true, if_false, reduceCtorEq, false_iff]
    intro hf
    rw [anyFilled_iff.2 hf] at h
    exact Bool.noConfusion h
  | true => simp only [if_true, true_iff]; exact anyFilled_iff.1 h

/-- What it answers is the twenty-third result of the result's states. -/
theorem readBack_some {X : FSt} {G : St} (h : readBack X = some G) : G = X.G ∧ ¬ X.HasFilled := by
  unfold readBack at h
  cases e : anyFilled X with
  | false =>
    rw [e] at h
    simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
    refine ⟨h.symm, fun hf => ?_⟩
    rw [anyFilled_iff.2 hf] at e
    exact Bool.noConfusion e
  | true =>
    rw [e] at h
    simp at h

/-- **The map back depends on the result only**: "none" on one state exactly when on another, and otherwise
two twenty-third states of one twenty-third result. -/
theorem readBack_congr {X Y : FSt} (s : Same24 X Y) :
    (readBack X = none ↔ readBack Y = none) ∧
      ∀ G H, readBack X = some G → readBack Y = some H → Same3 G H := by
  refine ⟨?_, fun G H hG hH => ?_⟩
  · rw [readBack_none_iff, readBack_none_iff]
    exact ⟨s.hasFilled, s.symm.hasFilled⟩
  · rw [(readBack_some hG).1, (readBack_some hH).1]
    exact s.1

theorem fc_pos {X : FSt} (h : X.HasFilled) : 1 ≤ X.fc := by
  obtain ⟨x, hx, fx⟩ := h
  have := rsum_le (f := fun y => if y = x then 1 else 0) (g := ind X.F) X.G.n (fun y _ => by
    unfold ind
    by_cases e : y = x
    · subst e
      rw [if_pos rfl, if_pos fx]
      exact Nat.le_refl 1
    · rw [if_neg e]
      omega)
  rw [rsum_point, if_pos hx] at this
  exact this

theorem n_le_phi (G : St) : G.n ≤ phi G := by
  unfold phi
  omega

/-- **Every result the map back answers "none" on costs at least two changes.** -/
theorem readBack_none_cost {X : FSt} (h : readBack X = none) {c : Nat} (hc : Cost24 X c) : 2 ≤ c := by
  obtain ⟨⟨Y, s, r⟩, _⟩ := hc
  have hf : Y.HasFilled := s.symm.hasFilled (readBack_none_iff.1 h)
  have a := r.pot_le empty24_wf
  rw [pot_empty] at a
  have b := fc_pos hf
  obtain ⟨x, hx, _⟩ := hf
  have d := n_le_phi Y.G
  unfold pot at a
  omega

theorem readBack_oneFilled : readBack oneFilled = none := rfl

/-- **The smallest result answered "none": one term, filled, nothing asserted, at cost two.** -/
theorem smallest_none : readBack oneFilled = none ∧ Cost24 oneFilled 2 := ⟨rfl, cost24_oneFilled⟩

/-- **… and the only one at cost two.** -/
theorem smallest_none_unique {X : FSt} (h : readBack X = none) (hc : Cost24 X 2) : Same24 X oneFilled := by
  obtain ⟨⟨Y, s, r⟩, _⟩ := hc
  have hf : Y.HasFilled := s.symm.hasFilled (readBack_none_iff.1 h)
  have hY := r.wf empty24_wf
  have a := r.pot_le empty24_wf
  rw [pot_empty] at a
  have b := fc_pos hf
  obtain ⟨x, hx, fx⟩ := hf
  unfold pot phi at a
  have hn : Y.G.n = 1 := by omega
  have hl : (plain Y.G.A).length = 0 := by omega
  have hp : plain Y.G.A = [] := List.eq_nil_of_length_eq_zero hl
  have sY : Same Y.G ⟨1, []⟩ := ⟨hn, by rw [hp]; exact List.Perm.refl _⟩
  have hx0 : x = 0 := by omega
  subst hx0
  refine s.symm.trans ⟨Same.same3 sY, fun z hz => ?_⟩
  have : z = 0 := by omega
  subst this
  rw [fx]
  rfl

/-- **The forgetting map merges results that differ only in their filled terms.** -/
theorem forget_merges : Same3 oneFilled.G (ofSt ⟨1, []⟩).G ∧ ¬ Same24 oneFilled (ofSt ⟨1, []⟩) := by
  refine ⟨Same3.refl _, fun h => ?_⟩
  have := h.2 0 (by decide)
  exact Bool.noConfusion this

end Twentyfourth
