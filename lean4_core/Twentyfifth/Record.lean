import Twentyfifth.Cost

/-!
# The twenty-third's record: whether, not which

The twenty-third recorded for a result its terms and the assertions in `r` and
in `s` of a state asserting the fewest (its reading C-R).  The task asks
whether that record shows which of a result's terms keep it from being the
result asserting nothing on as many terms.

Derived here:
* **it shows whether**: a result records no assertion — costs as many changes
  as it has terms — exactly when it is the result asserting nothing
  (`record_shows_whether`);
* **it does not show which**: `a b c; ara bsb`, `a b c; arb bsc` and
  `a b c; arb bsa` each assert the fewest of their results, one assertion in
  `r` and one in `s` — they record the same — and the first is kept from the
  result asserting nothing by a loop (one term), the second by a two-way sum
  with every loop zero (two terms), the third by a sum around three terms
  with every loop and two-way sum zero (three terms)
  (`record_does_not_show_which_terms`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

theorem sum_nine_ge' (a00 a01 a02 a10 a11 a12 a20 a21 a22 u v w : Nat) (hu : u ≤ a01 + a10) (hv : v ≤ a12 + a21)
    (hw : w ≤ a02 + a20) :
    3 + a00 + a11 + a22 + u + v + w ≤ 3 + (a00 + a01 + a02 + (a10 + a11 + a12) + (a20 + a21 + a22)) := by
  omega

/-- With three terms, the loops and the two-way sums bound `phi` below. -/
theorem phi_ge_sums3 {H : St} (hH : H.WF) (hn : H.n = 3) :
    3 + (excess H 0 0).natAbs + (excess H 1 1).natAbs + (excess H 2 2).natAbs +
        (excess H 0 1 + excess H 1 0).natAbs + (excess H 1 2 + excess H 2 1).natAbs +
        (excess H 0 2 + excess H 2 0).natAbs ≤ phi H := by
  rw [phi_eq_sum hH, hn, dsum_three]
  exact sum_nine_ge' _ _ _ _ _ _ _ _ _ _ _ _ (natAbs_add2 _ _) (natAbs_add2 _ _) (natAbs_add2 _ _)

/-- **With three terms, the cost is at least the terms plus the loops and the two-way sums.** -/
theorem cost3_three_ge_sums {G : St} (hn : G.n = 3) {c : Nat} (h : Cost3 G c) :
    3 + (excess G 0 0).natAbs + (excess G 1 1).natAbs + (excess G 2 2).natAbs +
        (excess G 0 1 + excess G 1 0).natAbs + (excess G 1 2 + excess G 2 1).natAbs +
        (excess G 0 2 + excess G 2 0).natAbs ≤ c := by
  obtain ⟨⟨H, hH, s, e⟩, _⟩ := cost3_iff.1 h
  have hHn : H.n = 3 := s.n.trans hn
  have b := phi_ge_sums3 hH hHn
  rw [s.loop (x := 0) (by omega), s.loop (x := 1) (by omega), s.loop (x := 2) (by omega),
    s.twoWay (x := 0) (y := 1) (by omega) (by omega), s.twoWay (x := 1) (y := 2) (by omega) (by omega),
    s.twoWay (x := 0) (y := 2) (by omega) (by omega)] at b
  omega

/-- `a b c; ara bsb`. -/
def wLoop : St := ⟨3, [⟨.r, 0, 0⟩, ⟨.s, 1, 1⟩]⟩

/-- `a b c; arb bsc`. -/
def wPair : St := ⟨3, [⟨.r, 0, 1⟩, ⟨.s, 1, 2⟩]⟩

theorem wLoop_wf : wLoop.WF := by
  intro a ha
  simp only [wLoop, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h <;> subst h <;> decide

theorem wPair_wf : wPair.WF := by
  intro a ha
  simp only [wPair, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h <;> subst h <;> decide

theorem arcThree_wf : arcThree.WF := by
  intro a ha
  simp only [arcThree, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h <;> subst h <;> decide

/-- A three-term state whose `phi` is the terms plus its loops and two-way sums costs `phi`. -/
theorem cost3_of_sums3 {G : St} (hG : G.WF) (hn : G.n = 3)
    (hp : phi G = 3 + (excess G 0 0).natAbs + (excess G 1 1).natAbs + (excess G 2 2).natAbs +
        (excess G 0 1 + excess G 1 0).natAbs + (excess G 1 2 + excess G 2 1).natAbs +
        (excess G 0 2 + excess G 2 0).natAbs) : Cost3 G (phi G) := by
  refine cost3_iff.2 ⟨⟨G, hG, Same3.refl _, rfl⟩, fun H hH s => ?_⟩
  have hHn : H.n = 3 := s.n.trans hn
  have b := phi_ge_sums3 hH hHn
  rw [s.loop (x := 0) (by omega), s.loop (x := 1) (by omega), s.loop (x := 2) (by omega),
    s.twoWay (x := 0) (y := 1) (by omega) (by omega), s.twoWay (x := 1) (y := 2) (by omega) (by omega),
    s.twoWay (x := 0) (y := 2) (by omega) (by omega)] at b
  omega

/-- A three-term state whose `phi` is the terms plus its sums around, both ways round, costs `phi`. -/
theorem cost3_of_around3 {G : St} (hG : G.WF) (hn : G.n = 3)
    (hp : phi G = 3 + (excess G 0 1 + excess G 1 2 + excess G 2 0).natAbs +
        (excess G 0 2 + excess G 2 1 + excess G 1 0).natAbs) : Cost3 G (phi G) := by
  refine cost3_iff.2 ⟨⟨G, hG, Same3.refl _, rfl⟩, fun H hH s => ?_⟩
  have hHn : H.n = 3 := s.n.trans hn
  have b := phi_ge_around hH hHn
  rw [s.around (x := 0) (y := 1) (z := 2) (by omega) (by omega) (by omega),
    s.around (x := 0) (y := 2) (z := 1) (by omega) (by omega) (by omega)] at b
  omega

theorem fewest_wLoop : Fewest wLoop :=
  (fewest_iff wLoop_wf).2 ⟨by decide, cost3_of_sums3 wLoop_wf rfl (by decide)⟩

theorem fewest_wPair : Fewest wPair :=
  (fewest_iff wPair_wf).2 ⟨by decide, cost3_of_sums3 wPair_wf rfl (by decide)⟩

theorem fewest_arcThree : Fewest arcThree :=
  (fewest_iff arcThree_wf).2 ⟨by decide, cost3_of_around3 arcThree_wf rfl (by decide)⟩

/-- **The twenty-third's record does not show which terms keep a result from being the one asserting
nothing.**  `a b c; ara bsb`, `a b c; arb bsc` and `a b c; arb bsa` each assert the fewest of their results,
with one assertion in `r` and one in `s`: they record the same.  The first is kept from the result asserting
nothing by a loop — one term; in the second every loop is zero and a two-way sum is not — two terms; in the
third every loop and every two-way sum is zero and a sum around three terms is not — three terms. -/
theorem record_does_not_show_which_terms :
    (Fewest wLoop ∧ Fewest wPair ∧ Fewest arcThree) ∧
    (wLoop.n = 3 ∧ wPair.n = 3 ∧ arcThree.n = 3) ∧
    ((wLoop.A.filter (fun a => a.q == .r)).length = 1 ∧ (wLoop.A.filter (fun a => a.q == .s)).length = 1 ∧
      (wPair.A.filter (fun a => a.q == .r)).length = 1 ∧ (wPair.A.filter (fun a => a.q == .s)).length = 1 ∧
      (arcThree.A.filter (fun a => a.q == .r)).length = 1 ∧ (arcThree.A.filter (fun a => a.q == .s)).length = 1) ∧
    excess wLoop 0 0 ≠ 0 ∧
    ((∀ x, x < 3 → excess wPair x x = 0) ∧ excess wPair 0 1 + excess wPair 1 0 ≠ 0) ∧
    ((∀ x, x < 3 → excess arcThree x x = 0) ∧
      (∀ x y, x < 3 → y < 3 → excess arcThree x y + excess arcThree y x = 0) ∧
      excess arcThree 0 1 + excess arcThree 1 2 + excess arcThree 2 0 ≠ 0) := by
  refine ⟨⟨fewest_wLoop, fewest_wPair, fewest_arcThree⟩, ⟨rfl, rfl, rfl⟩, by decide, by decide,
    ⟨fun x hx => ?_, by decide⟩, ⟨fun x hx => ?_, fun x y hx hy => ?_, by decide⟩⟩
  · rcases lt_three hx with rfl | rfl | rfl <;> decide
  · rcases lt_three hx with rfl | rfl | rfl <;> decide
  · rcases lt_three hx with rfl | rfl | rfl <;> rcases lt_three hy with rfl | rfl | rfl <;> decide

/-- `a b; ara`. -/
def aLoop : St := ⟨2, [⟨.r, 0, 0⟩]⟩

theorem aLoop_wf : aLoop.WF := by
  intro a ha
  simp only [aLoop, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  decide

/-- **The smallest pair**: `a b; ara` and `a b; arb` each assert the fewest of their results — one assertion,
in `r` — so they record the same; the first is kept from the result asserting nothing by a loop (one term),
the second, every loop zero, by a two-way sum (two terms). -/
theorem record_pair_two_terms :
    Fewest aLoop ∧ Fewest arbOnce ∧ aLoop.A.length = 1 ∧ arbOnce.A.length = 1 ∧
      excess aLoop 0 0 ≠ 0 ∧ (∀ x, x < 2 → excess arbOnce x x = 0) ∧ excess arbOnce 0 1 + excess arbOnce 1 0 ≠ 0 := by
  have c1 := cost3_two aLoop_wf rfl
  have e1 : 2 + (excess aLoop 0 0).natAbs + (excess aLoop 1 1).natAbs + (excess aLoop 0 1 + excess aLoop 1 0).natAbs =
      phi aLoop := by decide
  rw [e1] at c1
  have c2 := cost3_two arbOnce_wf rfl
  have e2 : 2 + (excess arbOnce 0 0).natAbs + (excess arbOnce 1 1).natAbs +
      (excess arbOnce 0 1 + excess arbOnce 1 0).natAbs = phi arbOnce := by decide
  rw [e2] at c2
  refine ⟨(fewest_iff aLoop_wf).2 ⟨by decide, c1⟩, (fewest_iff arbOnce_wf).2 ⟨by decide, c2⟩, rfl, rfl, by decide,
    fun x hx => ?_, by decide⟩
  rcases lt_two hx with rfl | rfl <;> decide

/-- A plain part that is empty means an excess of zero everywhere. -/
theorem excess_zero_of_plain_nil {H : St} (h : plain H.A = []) (x y : Nat) : excess H x y = 0 := by
  have c1 := count_plain H.A ⟨.r, x, y⟩
  have c2 := count_plain H.A ⟨.s, x, y⟩
  rw [h] at c1 c2
  simp only [Atom.partner, Rel.other, List.count_nil] at c1 c2
  unfold excess
  omega

/-- **The twenty-third's record shows whether**: a result records no assertion — costs as many changes as it
has terms — exactly when it is the result asserting nothing on as many terms. -/
theorem record_shows_whether {G : St} (hG : G.WF) : Cost3 G G.n ↔ Same3 G ⟨G.n, []⟩ := by
  have _ := hG
  constructor
  · intro h
    obtain ⟨⟨H, hH, s, e⟩, _⟩ := cost3_iff.1 h
    have hn : H.n = G.n := s.n
    have hl : (plain H.A).length = 0 := by
      simp only [phi] at e
      omega
    have hp : plain H.A = [] := by
      cases hq : plain H.A with
      | nil => rfl
      | cons b t => rw [hq] at hl; simp at hl
    have z : Same3 H ⟨H.n, []⟩ :=
      Same.same3 (same_iff_excess.2 ⟨rfl, fun x y => by rw [excess_zero_of_plain_nil hp x y]; rfl⟩)
    rw [hn] at z
    exact s.symm.trans z
  · intro h
    exact (Cost3.congr h).2 (cost3_nothing G.n)

end Twentyfifth
