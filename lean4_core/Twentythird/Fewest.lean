import Twentythird.Cost

/-!
# The states of a result asserting the fewest

`Fewest G`: no state of the result of `G` asserts fewer assertions than `G`.
Derived here:
* a state asserting the fewest asserts no pair in both relations
  (`Fewest.plain`), and its `phi` is the cost (`fewest_iff`);
* **with two terms**: a state asserting no pair in both relations asserts the
  fewest exactly when its two excesses between the terms have the same sign
  — no `xry` together with `ysx` (`fewest_two_iff`);
* **with four terms, single terms do not find the fewest**: on
  `a b c d; crd asb asc dsb dsc` raising no single term, and no three terms,
  lowers the count, while raising `a` and `d` lowers it from five to three
  (`four_single_terms_do_not_find_the_fewest`).  The general criterion (no set
  of terms whose raising lowers the count) is proved in the paper (D5).
-/

namespace Twentythird

open Twentysecond

/-- `G` asserts the fewest among the states of its result. -/
def Fewest (G : St) : Prop := G.WF ∧ ∀ H, H.WF → Same3 H G → G.A.length ≤ H.A.length

theorem length_ge_plain (G : St) : (plain G.A).length ≤ G.A.length := length_plain_le G.A

/-- **A state asserting the fewest asserts no pair in both relations.** -/
theorem Fewest.plain {G : St} (h : Fewest G) : together G.A = [] := by
  have hle := h.2 G.plainSt (plainSt_wf h.1) (Same.same3 (same_plainSt G).symm)
  have hs := length_split G.A
  simp only [St.plainSt] at hle
  cases e : together G.A with
  | nil => rfl
  | cons a t =>
    rw [e, List.length_cons] at hs
    omega

/-- **A state asserts the fewest exactly when it asserts no pair in both relations and its `phi` is the
cost of its result.** -/
theorem fewest_iff {G : St} (hG : G.WF) : Fewest G ↔ together G.A = [] ∧ Cost3 G (phi G) := by
  constructor
  · intro h
    refine ⟨h.plain, cost3_iff.2 ⟨⟨G, hG, Same3.refl G, rfl⟩, fun H hH s => ?_⟩⟩
    have a := h.2 H.plainSt (plainSt_wf hH) ((Same.same3 (same_plainSt H).symm).trans s)
    have b := length_split G.A
    rw [h.plain, List.length_nil] at b
    simp only [phi, St.plainSt, s.n] at a ⊢
    omega
  · rintro ⟨ht, hc⟩
    refine ⟨hG, fun H hH s => ?_⟩
    have a := (cost3_iff.1 hc).2 H hH s
    have b := length_split G.A
    rw [ht, List.length_nil] at b
    have c := length_plain_le H.A
    simp only [phi, s.n] at a
    omega

/-- **With two terms: a state asserting no pair in both relations asserts the fewest exactly when its two
excesses between the terms have the same sign** (no `xry` together with `ysx`). -/
theorem fewest_two_iff {G : St} (hG : G.WF) (hn : G.n = 2) (ht : together G.A = []) :
    Fewest G ↔ (0 ≤ excess G 0 1 ∧ 0 ≤ excess G 1 0) ∨ (excess G 0 1 ≤ 0 ∧ excess G 1 0 ≤ 0) := by
  have c2 := cost3_two hG hn
  have hp : phi G = 2 + ((excess G 0 0).natAbs + (excess G 0 1).natAbs +
      ((excess G 1 0).natAbs + (excess G 1 1).natAbs)) := by
    rw [phi_eq_sum hG, hn, dsum_two]
  rw [fewest_iff hG]
  constructor
  · rintro ⟨_, hc⟩
    have e := Cost3.unique hc c2
    by_cases a : 0 ≤ excess G 0 1
    · by_cases b : 0 ≤ excess G 1 0
      · exact Or.inl ⟨a, b⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · by_cases b : 0 ≤ excess G 1 0
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
  · intro h
    refine ⟨ht, ?_⟩
    have e : phi G = 2 + (excess G 0 0).natAbs + (excess G 1 1).natAbs + (excess G 0 1 + excess G 1 0).natAbs := by
      rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    rw [e]
    exact c2

/-- `a b c d; crd asb asc dsb dsc`. -/
def fourWitness : St := ⟨4, [⟨.r, 2, 3⟩, ⟨.s, 0, 1⟩, ⟨.s, 0, 2⟩, ⟨.s, 3, 1⟩, ⟨.s, 3, 2⟩]⟩

/-- Every term but `x` raised once. -/
def raiseAllBut (G : St) (x : Nat) : St := raiseTo G (fun y => if y = x then 0 else 1) G.n

theorem fourWitness_wf : fourWitness.WF := by
  intro a ha
  simp only [fourWitness, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h <;> subst h <;> decide

/-- **With four terms, single terms do not find the fewest**: raising one term, or every term but one,
never lowers the count of `a b c d; crd asb asc dsb dsc` (five assertions), while raising `a` and `d`
lowers it to three. -/
theorem four_single_terms_do_not_find_the_fewest :
    (∀ x, x < 4 → phi fourWitness ≤ phi (raise fourWitness x)) ∧
    (∀ x, x < 4 → phi fourWitness ≤ phi (raiseAllBut fourWitness x)) ∧
    phi (raise (raise fourWitness 0) 3) + 2 = phi fourWitness ∧
    ¬ Fewest fourWitness := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, by decide, fun h => ?_⟩
  · have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · have hR : (raise (raise fourWitness 0) 3).WF :=
      raise_wf (by decide) (raise_wf (by decide) fourWitness_wf)
    have s : Same3 (raise (raise fourWitness 0) 3) fourWitness :=
      ((same3_raise fourWitness 0).trans (same3_raise _ 3)).symm
    have := h.2 _ (plainSt_wf hR) ((Same.same3 (same_plainSt _).symm).trans s)
    exact absurd this (by decide)

end Twentythird
