import Twentyfourth.Tell

/-!
# The twenty-third's record: it shows whether, not which

The twenty-third records for a result its terms and the assertions in `r` and
in `s` of a state asserting the fewest (23:C-R, 23:D8).  The task asks
whether that record shows which terms keep a result from being the one
asserting nothing on as many terms.  Reading C-K of the paper: the terms that
keep it are those of the smallest sets on which it is not — a loop, two terms,
or three terms whose sum is not zero (23:D2).

Derived here:
* **the record shows whether** (`record_whether`): a result costs exactly its
  number of terms — records no assertion — exactly when it is the result
  asserting nothing;
* **the record does not show which**: `a b; ara` and `a b; arb` both assert
  the fewest of their results and record the same (two terms, one `r`, no
  `s`); the first is kept by one term, its loop, the second by no single
  term, only by two together (`record23_does_not_show_which`);
  `a b c; ara asb` and `a b c; arb bsa` record the same (three terms, one `r`,
  one `s`); the first is kept by one term, the second by no one term and no two
  terms, only by all three together (`record23_does_not_show_which_three`).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- What the twenty-third records for a result, read on a state of it: terms, assertions in `r`, in `s`. -/
def record23 (G : St) : Nat × Nat × Nat :=
  (G.n, (G.A.filter (fun a => decide (a.q = .r))).length, (G.A.filter (fun a => decide (a.q = .s))).length)

theorem phi_nothing (n : Nat) : phi ⟨n, []⟩ = n := rfl

/-- The result asserting nothing on `n` terms costs `n` changes. -/
theorem cost3_nothing (n : Nat) : Cost3 ⟨n, []⟩ n := by
  refine cost3_iff.2 ⟨⟨⟨n, []⟩, nothing_wf n, Same3.refl _, phi_nothing n⟩, fun H _ s => ?_⟩
  have := s.n
  simp only [phi]
  simp only at this
  omega

/-- **The twenty-third's record shows whether a result is the one asserting nothing**: it records no
assertion — the cost is the number of terms — exactly for that result. -/
theorem record_whether {G : St} : Cost3 G G.n ↔ Same3 G ⟨G.n, []⟩ := by
  constructor
  · intro h
    obtain ⟨⟨H, _, s, e⟩, _⟩ := cost3_iff.1 h
    have hn : H.n = G.n := s.n
    have hl : (plain H.A).length = 0 := by
      simp only [phi] at e
      omega
    have hp : plain H.A = [] := List.eq_nil_of_length_eq_zero hl
    have sH : Same H ⟨H.n, []⟩ := ⟨rfl, by rw [hp]; exact List.Perm.refl _⟩
    have e2 : (⟨H.n, []⟩ : St) = ⟨G.n, []⟩ := by rw [hn]
    rw [e2] at sH
    exact s.symm.trans (Same.same3 sH)
  · intro h
    exact (Cost3.congr h).2 (cost3_nothing G.n)

/-- `a b; ara`. -/
def loopA : St := ⟨2, [⟨.r, 0, 0⟩]⟩

/-- `a b; arb`. -/
def arbA : St := ⟨2, [⟨.r, 0, 1⟩]⟩

/-- `a b c; ara asb`. -/
def loopAsb : St := ⟨3, [⟨.r, 0, 0⟩, ⟨.s, 0, 1⟩]⟩

theorem length_pos_of_excess {H : St} {x y : Nat} (h : excess H x y ≠ 0) : 0 < H.A.length := by
  cases e : H.A with
  | nil =>
    exfalso
    apply h
    unfold excess
    rw [e]
    rfl
  | cons _ _ => simp

/-- On a well-formed state the assertions number at least `Σ |e(x, y)|`. -/
theorem dsum_le_length {H : St} (hw : H.WF) : dsum (fun x y => (excess H x y).natAbs) H.n ≤ H.A.length := by
  have a := phi_eq_sum hw
  have b := phi_le_size H
  simp only [St.size] at b
  omega

theorem loopA_wf : loopA.WF := by
  intro a ha
  simp only [loopA, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  decide

theorem arbA_wf : arbA.WF := by
  intro a ha
  simp only [arbA, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  decide

theorem loopAsb_wf : loopAsb.WF := by
  intro a ha
  simp only [loopAsb, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h <;> subst h <;> decide

theorem arcThree_wf : arcThree.WF := by
  intro a ha
  simp only [arcThree, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h <;> subst h <;> decide

theorem fewest_loopA : Fewest loopA := by
  refine ⟨loopA_wf, fun H _ s => ?_⟩
  have hn : H.n = 2 := s.n
  have e := s.loop (x := 0) (by omega)
  have := length_pos_of_excess (H := H) (x := 0) (y := 0) (by rw [e]; decide)
  show 1 ≤ H.A.length
  omega

theorem fewest_arbA : Fewest arbA := by
  refine ⟨arbA_wf, fun H _ s => ?_⟩
  have hn : H.n = 2 := s.n
  have e := s.twoWay (x := 0) (y := 1) (by omega) (by omega)
  have e1 : excess arbA 0 1 + excess arbA 1 0 = 1 := by decide
  show 1 ≤ H.A.length
  by_cases h : excess H 0 1 = 0
  · have := length_pos_of_excess (H := H) (x := 1) (y := 0) (by omega)
    omega
  · have := length_pos_of_excess h
    omega

theorem fewest_loopAsb : Fewest loopAsb := by
  refine ⟨loopAsb_wf, fun H hH s => ?_⟩
  have hn : H.n = 3 := s.n
  have l := s.loop (x := 0) (by omega)
  have t := s.twoWay (x := 0) (y := 1) (by omega) (by omega)
  have el : excess loopAsb 0 0 = 1 := by decide
  have et : excess loopAsb 0 1 + excess loopAsb 1 0 = -1 := by decide
  have d := dsum_le_length hH
  rw [hn, dsum_three] at d
  show 2 ≤ H.A.length
  omega

theorem fewest_arcThree : Fewest arcThree := by
  refine ⟨arcThree_wf, fun H hH s => ?_⟩
  have hn : H.n = 3 := s.n
  have a := s.around (x := 0) (y := 1) (z := 2) (by omega) (by omega) (by omega)
  have b := s.around (x := 0) (y := 2) (z := 1) (by omega) (by omega) (by omega)
  have ea : excess arcThree 0 1 + excess arcThree 1 2 + excess arcThree 2 0 = 1 := by decide
  have eb : excess arcThree 0 2 + excess arcThree 2 1 + excess arcThree 1 0 = -1 := by decide
  have c := phi_ge_around hH hn
  have d := phi_le_size H
  simp only [St.size] at d
  show 2 ≤ H.A.length
  omega

/-- **The twenty-third's record does not show which terms keep a result from being the one asserting
nothing**: two results asserting the fewest with one record, the first kept by one term, the second only by
two terms together. -/
theorem record23_does_not_show_which :
    Fewest loopA ∧ Fewest arbA ∧ record23 loopA = record23 arbA ∧
    excess loopA 0 0 ≠ 0 ∧ (∀ x, x < 2 → excess arbA x x = 0) ∧ excess arbA 0 1 + excess arbA 1 0 ≠ 0 := by
  refine ⟨fewest_loopA, fewest_arbA, by decide, by decide, fun x hx => ?_, by decide⟩
  rcases lt_two hx with rfl | rfl <;> decide

/-- **… and with three terms**: one record, the first kept by one term, the second by no one term and no
two terms, only by all three together. -/
theorem record23_does_not_show_which_three :
    Fewest loopAsb ∧ Fewest arcThree ∧ record23 loopAsb = record23 arcThree ∧
    excess loopAsb 0 0 ≠ 0 ∧ (∀ x, x < 3 → excess arcThree x x = 0) ∧
    (∀ x y, x < 3 → y < 3 → excess arcThree x y + excess arcThree y x = 0) ∧ ¬ Same3 arcThree ⟨3, []⟩ := by
  refine ⟨fewest_loopAsb, fewest_arcThree, by decide, by decide, fun x hx => ?_, fun x y hx hy => ?_,
    arcThree_not_nothing⟩
  · rcases lt_three hx with rfl | rfl | rfl <;> decide
  · rcases lt_three hx with rfl | rfl | rfl <;> rcases lt_three hy with rfl | rfl | rfl <;> decide

end Twentyfourth
