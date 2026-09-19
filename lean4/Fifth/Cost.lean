import Fifth.Step

/-!
# Fewest changes under the fifth seed: the size difference plus twice the destroyed givens

The first derivation's potential, on counted states: `lostA5 s` counts the givens
that `s` has destroyed when `bra` was not asserted to begin with (`arb` at
multiplicity zero: 1; `a` and `b` one term: 2), `lostB5` does the same when `bra`
was asserted; `costA5 s = size s + 2 * lostA5 s`, size counting multiplicities.

Derived here:
* one performed change raises the cost by at most one (`Step5.costA_le`,
  `Step5.costB_le`): a term or an assertion raises the size by one and destroys
  nothing; a removal lowers the size by one and destroys at most one given; an
  identification lowers the size by one (the total multiplicity is kept,
  `total_identify`) and destroys at most one given (it merges `a` and `b` only
  when nothing is asserted between them, and otherwise a merged multiplicity is
  at least each part, `identify_M_ge`);
* so a state reached from what is given in `n` changes has cost at most `n` plus
  the cost of what is given (`fewest_changes5_lower_A`, `_B`);
* the bound is attained: remove the given assertions the target lacks (and
  identify `a`, `b` if the target has them one term), then the fourth
  derivation's additions (`reach4_of_contains`, through `Reach4.toReach5`);
  `fewest_changes5_A`, `fewest_changes5_B`;
* on a state containing what is given the destroyed givens are zero, so the
  fewest changes is the size difference: the fourth derivation's cost survives
  there (`fewest_changes5_of_contains_A`, `_B`) — and only there: the size can
  fall along a change (`size_can_fall`);
* every change moves the size by exactly one either way, so the size and the
  length of a sequence have a fixed parity (`Step5.size_step`,
  `Reach5.size_parity`): no change keeps the cost, and a sequence of changes
  between two states has the parity of their size difference.

Cited from the first derivation and re-checked: `Step.costA_le` and the edit
path are the model for the proofs; they are re-proved here because a removal
now lowers a multiplicity by one instead of un-asserting, and an identification
adds multiplicities up.  Cited from the fourth derivation and re-checked:
`reach4_of_contains` (additions reach everything containing the state) is used
as it stands, through the embedding, for the upper bound.
-/

namespace Seed.Fifth

open Seed Seed.Fourth MSt

/-- `1` if `xry` is not asserted, `0` if it is. -/
def miss5 (s : MSt) (x y : ℕ) : ℕ := if s.M (x, y) = 0 then 1 else 0

/-- Destroyed givens, when what is given is `arb` alone. -/
def lostA5 (s : MSt) : ℕ := if s.a = s.b then 2 else miss5 s s.a s.b

/-- Destroyed givens, when `arb` and `bra` were asserted to begin with. -/
def lostB5 (s : MSt) : ℕ := if s.a = s.b then 3 else miss5 s s.a s.b + miss5 s s.b s.a

/-- Size (multiplicities counted) plus two for each destroyed given (`bra` not given). -/
def costA5 (s : MSt) : ℕ := s.size + 2 * lostA5 s

/-- Size plus two for each destroyed given (`bra` given). -/
def costB5 (s : MSt) : ℕ := s.size + 2 * lostB5 s

/-! ## The destroyed givens -/

theorem miss5_of_ne_zero {s : MSt} {x y : ℕ} (h : s.M (x, y) ≠ 0) : miss5 s x y = 0 := by
  simp [miss5, h]

theorem miss5_of_zero {s : MSt} {x y : ℕ} (h : s.M (x, y) = 0) : miss5 s x y = 1 := by
  simp [miss5, h]

theorem miss5_le_one (s : MSt) (x y : ℕ) : miss5 s x y ≤ 1 := by
  unfold miss5
  split_ifs <;> omega

/-- A multiplicity that does not fall cannot make a given missing. -/
theorem miss5_le_of_le {s t : MSt} {x y x' y' : ℕ} (h : s.M (x, y) ≤ t.M (x', y')) :
    miss5 t x' y' ≤ miss5 s x y := by
  unfold miss5
  split_ifs <;> omega

theorem lostA5_of_eq {s : MSt} (h : s.a = s.b) : lostA5 s = 2 := by simp [lostA5, h]
theorem lostA5_of_ne {s : MSt} (h : s.a ≠ s.b) : lostA5 s = miss5 s s.a s.b := by simp [lostA5, h]
theorem lostB5_of_eq {s : MSt} (h : s.a = s.b) : lostB5 s = 3 := by simp [lostB5, h]
theorem lostB5_of_ne {s : MSt} (h : s.a ≠ s.b) : lostB5 s = miss5 s s.a s.b + miss5 s s.b s.a := by
  simp [lostB5, h]

theorem lostA5_le_two (s : MSt) : lostA5 s ≤ 2 := by
  by_cases h : s.a = s.b
  · rw [lostA5_of_eq h]
  · have := miss5_le_one s s.a s.b
    rw [lostA5_of_ne h]
    omega

theorem lostB5_le_three (s : MSt) : lostB5 s ≤ 3 := by
  by_cases h : s.a = s.b
  · rw [lostB5_of_eq h]
  · have h1 := miss5_le_one s s.a s.b
    have h2 := miss5_le_one s s.b s.a
    rw [lostB5_of_ne h]
    omega

/-- An addition destroys nothing: its state is contained in its outcome. -/
theorem lostA5_le_of_contains {s t : MSt} (h : Contains4 s t) : lostA5 t ≤ lostA5 s := by
  rw [lostA5, lostA5, h.name_a, h.name_b]
  split_ifs
  · exact le_refl _
  · exact miss5_le_of_le (h.mult _)

theorem lostB5_le_of_contains {s t : MSt} (h : Contains4 s t) : lostB5 t ≤ lostB5 s := by
  rw [lostB5, lostB5, h.name_a, h.name_b]
  split_ifs
  · exact le_refl _
  · exact Nat.add_le_add (miss5_le_of_le (h.mult _)) (miss5_le_of_le (h.mult _))

/-- Removing another assertion leaves `xry` as it was. -/
theorem miss5_remove_of_ne {s : MSt} {x y u v : ℕ} (h : (u, v) ≠ (x, y)) :
    miss5 (s.remove x y) u v = miss5 s u v := by
  unfold miss5
  rw [remove_M_of_ne s x y h]

theorem miss5_remove_le (s : MSt) (x y u v : ℕ) : miss5 (s.remove x y) u v ≤ miss5 s u v + 1 := by
  have := miss5_le_one (s.remove x y) u v
  omega

theorem lostA5_remove (s : MSt) (x y : ℕ) : lostA5 (s.remove x y) ≤ lostA5 s + 1 := by
  by_cases h : s.a = s.b
  · rw [lostA5_of_eq (s := s.remove x y) h, lostA5_of_eq h]
    omega
  · rw [lostA5_of_ne (s := s.remove x y) h, lostA5_of_ne h]
    exact miss5_remove_le s x y s.a s.b

/-- One removal destroys at most one given: it cannot be both `arb` and `bra`. -/
theorem lostB5_remove (s : MSt) (x y : ℕ) : lostB5 (s.remove x y) ≤ lostB5 s + 1 := by
  by_cases h : s.a = s.b
  · rw [lostB5_of_eq (s := s.remove x y) h, lostB5_of_eq h]
    omega
  · rw [lostB5_of_ne (s := s.remove x y) h, lostB5_of_ne h]
    by_cases h1 : (s.a, s.b) = (x, y)
    · have h2 : (s.b, s.a) ≠ (x, y) := by
        intro h2
        rw [← h1] at h2
        exact h (Prod.mk.inj h2).1.symm
      have e := miss5_remove_of_ne (s := s) h2
      have le := miss5_remove_le s x y s.a s.b
      show miss5 (s.remove x y) s.a s.b + miss5 (s.remove x y) s.b s.a ≤ _
      rw [e]
      omega
    · have e := miss5_remove_of_ne (s := s) h1
      have le := miss5_remove_le s x y s.b s.a
      show miss5 (s.remove x y) s.a s.b + miss5 (s.remove x y) s.b s.a ≤ _
      rw [e]
      omega

/-- An unobstructed identification destroys at most one given: it merges `a` and `b`
only when nothing is asserted between them, and otherwise a merged multiplicity is at
least each part. -/
theorem lostA5_identify {s : MSt} (hw : s.WF) {u v : ℕ} (_huv : u ≠ v) (h1 : s.M (u, v) = 0)
    (h2 : s.M (v, u) = 0) : lostA5 (s.identify u v) ≤ lostA5 s + 1 := by
  by_cases hab : s.a = s.b
  · have h' : (s.identify u v).a = (s.identify u v).b := by simp [hab]
    rw [lostA5_of_eq h', lostA5_of_eq hab]
    omega
  · by_cases hab' : (s.identify u v).a = (s.identify u v).b
    · have := lostA5_le_two (s.identify u v)
      rw [lostA5_of_ne hab]
      simp only [identify_a, identify_b] at hab'
      rcases merge_eq_merge hab hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [miss5_of_zero (by rw [ha, hb]; exact h1)]
        omega
      · rw [miss5_of_zero (by rw [ha, hb]; exact h2)]
        omega
    · rw [lostA5_of_ne hab', lostA5_of_ne hab]
      simp only [identify_a, identify_b]
      have e := miss5_le_of_le (identify_M_ge s u v hw.2.1 hw.2.2)
      omega

theorem lostB5_identify {s : MSt} (hw : s.WF) {u v : ℕ} (_huv : u ≠ v) (h1 : s.M (u, v) = 0)
    (h2 : s.M (v, u) = 0) : lostB5 (s.identify u v) ≤ lostB5 s + 1 := by
  by_cases hab : s.a = s.b
  · have h' : (s.identify u v).a = (s.identify u v).b := by simp [hab]
    rw [lostB5_of_eq h', lostB5_of_eq hab]
    omega
  · by_cases hab' : (s.identify u v).a = (s.identify u v).b
    · have := lostB5_le_three (s.identify u v)
      rw [lostB5_of_ne hab]
      simp only [identify_a, identify_b] at hab'
      rcases merge_eq_merge hab hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [miss5_of_zero (by rw [ha, hb]; exact h1), miss5_of_zero (by rw [ha, hb]; exact h2)]
        omega
      · rw [miss5_of_zero (by rw [ha, hb]; exact h2), miss5_of_zero (by rw [ha, hb]; exact h1)]
        omega
    · rw [lostB5_of_ne hab', lostB5_of_ne hab]
      simp only [identify_a, identify_b]
      have e1 := miss5_le_of_le (identify_M_ge s u v hw.2.1 hw.2.2)
      have e2 := miss5_le_of_le (identify_M_ge s u v hw.2.2 hw.2.1)
      omega

/-! ## One change raises the cost by at most one -/

theorem Step5.costA_le {s t : MSt} (h : Step5 s t) (hw : s.WF) : costA5 t ≤ costA5 s + 1 := by
  unfold costA5
  cases h with
  | addTerm t ht =>
    have e := Seed.Fourth.size_addTerm hw ht
    have l := lostA5_le_of_contains (Step4.addTerm s t ht).contains
    omega
  | addAssertion x y hx hy hxy =>
    have e := Seed.Fourth.size_addAssertion hx hy
    have l := lostA5_le_of_contains (Step4.addAssertion s x y hx hy hxy).contains
    omega
  | remove x y hp =>
    have hxy : x ∈ s.T ∧ y ∈ s.T := hw.1 (x, y) hp
    have e := size_remove s hxy.1 hxy.2 hp
    have l := lostA5_remove s x y
    omega
  | identify u v hu hv huv h1 h2 =>
    have e := size_identify s hu hv huv
    have l := lostA5_identify hw huv h1 h2
    omega

theorem Step5.costB_le {s t : MSt} (h : Step5 s t) (hw : s.WF) : costB5 t ≤ costB5 s + 1 := by
  unfold costB5
  cases h with
  | addTerm t ht =>
    have e := Seed.Fourth.size_addTerm hw ht
    have l := lostB5_le_of_contains (Step4.addTerm s t ht).contains
    omega
  | addAssertion x y hx hy hxy =>
    have e := Seed.Fourth.size_addAssertion hx hy
    have l := lostB5_le_of_contains (Step4.addAssertion s x y hx hy hxy).contains
    omega
  | remove x y hp =>
    have hxy : x ∈ s.T ∧ y ∈ s.T := hw.1 (x, y) hp
    have e := size_remove s hxy.1 hxy.2 hp
    have l := lostB5_remove s x y
    omega
  | identify u v hu hv huv h1 h2 =>
    have e := size_identify s hu hv huv
    have l := lostB5_identify hw huv h1 h2
    omega

theorem Reach5.costA_le {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hw : s.WF) :
    costA5 t ≤ costA5 s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costA_le (r.wf hw)
    omega

theorem Reach5.costB_le {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hw : s.WF) :
    costB5 t ≤ costB5 s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costB_le (r.wf hw)
    omega

/-! ## Every change moves the size by one: parity -/

theorem Step5.size_step {s t : MSt} (h : Step5 s t) (hw : s.WF) :
    t.size = s.size + 1 ∨ t.size + 1 = s.size := by
  cases h with
  | addTerm t ht => exact Or.inl (Seed.Fourth.size_addTerm hw ht)
  | addAssertion x y hx hy hxy => exact Or.inl (Seed.Fourth.size_addAssertion hx hy)
  | remove x y hp =>
    have hxy : x ∈ s.T ∧ y ∈ s.T := hw.1 (x, y) hp
    exact Or.inr (size_remove s hxy.1 hxy.2 hp)
  | identify u v hu hv huv h1 h2 => exact Or.inr (size_identify s hu hv huv)

/-- The size and the length of a sequence have a fixed parity: `size(t) − size(s)` and
`n` are even together.  So no change keeps the cost where it was. -/
theorem Reach5.size_parity {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hw : s.WF) :
    (s.size + t.size + n) % 2 = 0 := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step (r.wf hw) with e | e <;> omega

/-! ## What is given -/

theorem lostA5_givenA4 : lostA5 givenA4 = 0 := by
  rw [lostA5_of_ne (by rw [givenA4_a, givenA4_b]; omega), miss5_of_ne_zero givenA4_arb_ne]

theorem lostB5_givenB4 : lostB5 givenB4 = 0 := by
  rw [lostB5_of_ne (by rw [givenB4_a, givenB4_b]; omega), miss5_of_ne_zero givenB4_arb_ne,
    miss5_of_ne_zero givenB4_bra_ne]

theorem costA5_givenA4 : costA5 givenA4 = 3 := by
  rw [costA5, size_givenA4, lostA5_givenA4]

theorem costB5_givenB4 : costB5 givenB4 = 4 := by
  rw [costB5, size_givenB4, lostB5_givenB4]

/-- **Lower bound, `bra` not asserted to begin with.** -/
theorem fewest_changes5_lower_A {t : MSt} {n : ℕ} (h : Reach5 givenA4 t n) : costA5 t ≤ n + 3 := by
  have := h.costA_le givenA4_wf
  rw [costA5_givenA4] at this
  omega

/-- **Lower bound, `bra` asserted to begin with.** -/
theorem fewest_changes5_lower_B {t : MSt} {n : ℕ} (h : Reach5 givenB4 t n) : costB5 t ≤ n + 4 := by
  have := h.costB_le givenB4_wf
  rw [costB5_givenB4] at this
  omega

/-! ## Upper bound: remove the missing givens, then add -/

theorem mem_givenA4_T (x : ℕ) : x ∈ givenA4.T ↔ x = 0 ∨ x = 1 := by
  simp [givenA4, ofSt, givenA]

theorem mem_givenB4_T (x : ℕ) : x ∈ givenB4.T ↔ x = 0 ∨ x = 1 := by
  simp [givenB4, ofSt, givenB]

theorem givenA4_M (p : ℕ × ℕ) : givenA4.M p = if p ∈ givenA.A then 1 else 0 := rfl
theorem givenB4_M (p : ℕ × ℕ) : givenB4.M p = if p ∈ givenB.A then 1 else 0 := rfl

/-- Removing `arb` from what is given: the state with the given terms and nothing asserted. -/
theorem removed_arb_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1) :
    Contains4 (givenA4.remove 0 1) g := by
  refine ⟨given_terms_subset (toSt_wf hgw) ha hb, fun p => ?_, ha, hb⟩
  rw [remove_M, Function.update_apply]
  split_ifs with hp
  · exact Nat.zero_le _
  · rw [givenA4_M]
    simp [givenA, hp]

theorem size_removed_arb : (givenA4.remove 0 1).size = 2 := by
  have := size_remove givenA4 (x := 0) (y := 1) ((mem_givenA4_T 0).2 (Or.inl rfl))
    ((mem_givenA4_T 1).2 (Or.inr rfl)) (by rw [givenA4_arb]; omega)
  rw [size_givenA4] at this
  omega

theorem step_remove_arb : Step5 givenA4 (givenA4.remove 0 1) :=
  Step5.remove _ 0 1 (by rw [givenA4_arb]; omega)

/-- **Upper bound, `a` and `b` apart, `bra` not asserted to begin with.** -/
theorem fewest_changes5_upper_A_apart {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1) : ∃ n, Reach5 givenA4 g n ∧ n + 3 = costA5 g := by
  have hne : g.a ≠ g.b := by rw [ha, hb]; omega
  by_cases hab : g.M (0, 1) = 0
  · have hw1 : (givenA4.remove 0 1).WF := step_remove_arb.wf givenA4_wf
    obtain ⟨n, hn, hc⟩ := reach4_of_contains hw1 hg hgw (removed_arb_contains hgw ha hb)
    refine ⟨1 + n, (Reach5.single step_remove_arb).trans hn.toReach5, ?_⟩
    rw [size_removed_arb] at hc
    unfold costA5
    rw [lostA5_of_ne hne, miss5_of_zero (by rw [ha, hb]; exact hab)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach4_of_contains givenA4_wf hg hgw (givenA4_contains hgw ha hb hab)
    refine ⟨n, hn.toReach5, ?_⟩
    rw [size_givenA4] at hc
    unfold costA5
    rw [lostA5_of_ne hne, miss5_of_ne_zero (by rw [ha, hb]; exact hab)]
    omega

theorem oneTerm4_wf : oneTerm4.WF := by
  refine ⟨fun p hp => ?_, by simp [oneTerm4, ofSt, oneTerm], by simp [oneTerm4, ofSt, oneTerm]⟩
  simp [oneTerm4, ofSt, oneTerm] at hp

theorem size_oneTerm4 : oneTerm4.size = 1 := by decide

theorem oneTerm4_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 0) :
    Contains4 oneTerm4 g := by
  refine ⟨fun t ht => ?_, fun p => ?_, ha, hb⟩
  · have : t = 0 := by simpa [oneTerm4, ofSt, oneTerm] using ht
    subst this
    exact ha ▸ hgw.2.1
  · show (if p ∈ oneTerm.A then 1 else 0) ≤ g.M p
    simp [oneTerm]

/-- Removing `arb` and then identifying `a` and `b`: two changes to the one-term state. -/
theorem givenA4_to_oneTerm4 : Reach5 givenA4 oneTerm4 2 := by
  have st2 : Step5 (givenA4.remove 0 1) ((givenA4.remove 0 1).identify 0 1) :=
    Step5.identify _ 0 1 ((mem_givenA4_T 0).2 (Or.inl rfl)) ((mem_givenA4_T 1).2 (Or.inr rfl))
      (by omega) (by rw [remove_M_self, givenA4_arb]) (by rw [remove_M_of_ne _ _ _ (by decide), givenA4_bra])
  have e : (givenA4.remove 0 1).identify 0 1 = oneTerm4 := by
    apply MSt.ext
    · show ({0, 1} : Finset ℕ).erase 1 = {0}
      decide
    · funext p
      rw [identify_M]
      show _ = (if p ∈ oneTerm.A then 1 else 0)
      simp only [oneTerm, Finset.notMem_empty, if_false]
      apply Finset.sum_eq_zero
      intro q _
      rw [remove_M, Function.update_apply]
      split_ifs with h
      · rw [givenA4_arb]
        rfl
      · rw [givenA4_M]
        simp [givenA, h]
    · rfl
    · rfl
  exact e ▸ Reach5.step (Reach5.single step_remove_arb) st2

/-- **Upper bound, `a` and `b` identified, `bra` not asserted to begin with.** -/
theorem fewest_changes5_upper_A_merged {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 0) : ∃ n, Reach5 givenA4 g n ∧ n + 3 = costA5 g := by
  obtain ⟨n, hn, hc⟩ := reach4_of_contains oneTerm4_wf hg hgw (oneTerm4_contains hgw ha hb)
  refine ⟨2 + n, givenA4_to_oneTerm4.trans hn.toReach5, ?_⟩
  rw [size_oneTerm4] at hc
  unfold costA5
  rw [lostA5_of_eq (ha.trans hb.symm)]
  omega

/-- **Fewest changes, `bra` not asserted to begin with.**  A legal state written with
`a = 0` and `b ∈ {0, 1}` is reached in exactly `costA5 g − 3` changes and no fewer. -/
theorem fewest_changes5_A {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach5 givenA4 g n ∧ n + 3 = costA5 g) ∧ ∀ n, Reach5 givenA4 g n → costA5 g ≤ n + 3 :=
  ⟨hb.elim (fewest_changes5_upper_A_apart hg hgw ha) (fewest_changes5_upper_A_merged hg hgw ha),
    fun _ h => fewest_changes5_lower_A h⟩

/-! ### With `bra` given -/

theorem step_remove_arb_B : Step5 givenB4 (givenB4.remove 0 1) :=
  Step5.remove _ 0 1 (by rw [givenB4_arb]; omega)

theorem step_remove_bra_B : Step5 givenB4 (givenB4.remove 1 0) :=
  Step5.remove _ 1 0 (by rw [givenB4_bra]; omega)

theorem step_remove_both_B : Step5 (givenB4.remove 0 1) ((givenB4.remove 0 1).remove 1 0) :=
  Step5.remove _ 1 0 (by rw [remove_M_of_ne _ _ _ (by decide), givenB4_bra]; omega)

theorem size_givenB4_remove_arb : (givenB4.remove 0 1).size = 3 := by
  have := size_remove givenB4 (x := 0) (y := 1) ((mem_givenB4_T 0).2 (Or.inl rfl))
    ((mem_givenB4_T 1).2 (Or.inr rfl)) (by rw [givenB4_arb]; omega)
  rw [size_givenB4] at this
  omega

theorem size_givenB4_remove_bra : (givenB4.remove 1 0).size = 3 := by
  have := size_remove givenB4 (x := 1) (y := 0) ((mem_givenB4_T 1).2 (Or.inr rfl))
    ((mem_givenB4_T 0).2 (Or.inl rfl)) (by rw [givenB4_bra]; omega)
  rw [size_givenB4] at this
  omega

theorem size_givenB4_remove_both : ((givenB4.remove 0 1).remove 1 0).size = 2 := by
  have := size_remove (givenB4.remove 0 1) (x := 1) (y := 0) ((mem_givenB4_T 1).2 (Or.inr rfl))
    ((mem_givenB4_T 0).2 (Or.inl rfl)) (by rw [remove_M_of_ne _ _ _ (by decide), givenB4_bra]; omega)
  rw [size_givenB4_remove_arb] at this
  omega

theorem givenB4_remove_arb_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hba : g.M (1, 0) ≠ 0) : Contains4 (givenB4.remove 0 1) g := by
  refine ⟨given_terms_subset (toSt_wf hgw) ha hb, fun p => ?_, ha, hb⟩
  rw [remove_M, Function.update_apply]
  split_ifs with hp
  · exact Nat.zero_le _
  · rw [givenB4_M]
    simp only [givenB, Finset.mem_insert, Finset.mem_singleton]
    split_ifs with hq
    · rcases hq with rfl | rfl
      · exact absurd rfl hp
      · omega
    · exact Nat.zero_le _

theorem givenB4_remove_bra_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : g.M (0, 1) ≠ 0) : Contains4 (givenB4.remove 1 0) g := by
  refine ⟨given_terms_subset (toSt_wf hgw) ha hb, fun p => ?_, ha, hb⟩
  rw [remove_M, Function.update_apply]
  split_ifs with hp
  · exact Nat.zero_le _
  · rw [givenB4_M]
    simp only [givenB, Finset.mem_insert, Finset.mem_singleton]
    split_ifs with hq
    · rcases hq with rfl | rfl
      · omega
      · exact absurd rfl hp
    · exact Nat.zero_le _

theorem givenB4_remove_both_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1) :
    Contains4 ((givenB4.remove 0 1).remove 1 0) g := by
  refine ⟨given_terms_subset (toSt_wf hgw) ha hb, fun p => ?_, ha, hb⟩
  rw [remove_M, Function.update_apply]
  split_ifs with hp
  · exact Nat.zero_le _
  · rw [remove_M, Function.update_apply]
    split_ifs with hp'
    · exact Nat.zero_le _
    · rw [givenB4_M]
      simp only [givenB, Finset.mem_insert, Finset.mem_singleton]
      split_ifs with hq
      · rcases hq with rfl | rfl
        · exact absurd rfl hp'
        · exact absurd rfl hp
      · exact Nat.zero_le _

/-- **Upper bound, `a` and `b` apart, `bra` asserted to begin with.** -/
theorem fewest_changes5_upper_B_apart {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1) : ∃ n, Reach5 givenB4 g n ∧ n + 4 = costB5 g := by
  have hne : g.a ≠ g.b := by rw [ha, hb]; omega
  unfold costB5
  rw [lostB5_of_ne hne]
  by_cases hab : g.M (0, 1) = 0 <;> by_cases hba : g.M (1, 0) = 0
  · obtain ⟨n, hn, hc⟩ := reach4_of_contains (step_remove_both_B.wf (step_remove_arb_B.wf givenB4_wf))
      hg hgw (givenB4_remove_both_contains hgw ha hb)
    refine ⟨2 + n, ((Reach5.single step_remove_arb_B).step step_remove_both_B).trans hn.toReach5, ?_⟩
    rw [size_givenB4_remove_both] at hc
    rw [miss5_of_zero (by rw [ha, hb]; exact hab), miss5_of_zero (by rw [ha, hb]; exact hba)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach4_of_contains (step_remove_arb_B.wf givenB4_wf) hg hgw
      (givenB4_remove_arb_contains hgw ha hb hba)
    refine ⟨1 + n, (Reach5.single step_remove_arb_B).trans hn.toReach5, ?_⟩
    rw [size_givenB4_remove_arb] at hc
    rw [miss5_of_zero (by rw [ha, hb]; exact hab), miss5_of_ne_zero (by rw [ha, hb]; exact hba)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach4_of_contains (step_remove_bra_B.wf givenB4_wf) hg hgw
      (givenB4_remove_bra_contains hgw ha hb hab)
    refine ⟨1 + n, (Reach5.single step_remove_bra_B).trans hn.toReach5, ?_⟩
    rw [size_givenB4_remove_bra] at hc
    rw [miss5_of_ne_zero (by rw [ha, hb]; exact hab), miss5_of_zero (by rw [ha, hb]; exact hba)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach4_of_contains givenB4_wf hg hgw (givenB4_contains hgw ha hb hab hba)
    refine ⟨n, hn.toReach5, ?_⟩
    rw [size_givenB4] at hc
    rw [miss5_of_ne_zero (by rw [ha, hb]; exact hab), miss5_of_ne_zero (by rw [ha, hb]; exact hba)]
    omega

/-- Removing `arb`, removing `bra`, then identifying `a` and `b`: three changes to the
one-term state. -/
theorem givenB4_to_oneTerm4 : Reach5 givenB4 oneTerm4 3 := by
  have st3 : Step5 ((givenB4.remove 0 1).remove 1 0) (((givenB4.remove 0 1).remove 1 0).identify 0 1) :=
    Step5.identify _ 0 1 ((mem_givenB4_T 0).2 (Or.inl rfl)) ((mem_givenB4_T 1).2 (Or.inr rfl))
      (by omega) (by rw [remove_M_of_ne _ _ _ (by decide), remove_M_self, givenB4_arb])
      (by rw [remove_M_self, remove_M_of_ne _ _ _ (by decide), givenB4_bra])
  have e : ((givenB4.remove 0 1).remove 1 0).identify 0 1 = oneTerm4 := by
    apply MSt.ext
    · show ({0, 1} : Finset ℕ).erase 1 = {0}
      decide
    · funext p
      rw [identify_M]
      show _ = (if p ∈ oneTerm.A then 1 else 0)
      simp only [oneTerm, Finset.notMem_empty, if_false]
      apply Finset.sum_eq_zero
      intro q _
      rw [remove_M, Function.update_apply]
      split_ifs with h
      · rw [remove_M_of_ne _ _ _ (by decide), givenB4_bra]
        rfl
      · rw [remove_M, Function.update_apply]
        split_ifs with h'
        · rw [givenB4_arb]
          rfl
        · rw [givenB4_M]
          simp only [givenB, Finset.mem_insert, Finset.mem_singleton]
          split_ifs with hq
          · rcases hq with rfl | rfl
            · exact absurd rfl h'
            · exact absurd rfl h
          · rfl
    · rfl
    · rfl
  exact e ▸ Reach5.step ((Reach5.single step_remove_arb_B).step step_remove_both_B) st3

/-- **Upper bound, `a` and `b` identified, `bra` asserted to begin with.** -/
theorem fewest_changes5_upper_B_merged {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 0) : ∃ n, Reach5 givenB4 g n ∧ n + 4 = costB5 g := by
  obtain ⟨n, hn, hc⟩ := reach4_of_contains oneTerm4_wf hg hgw (oneTerm4_contains hgw ha hb)
  refine ⟨3 + n, givenB4_to_oneTerm4.trans hn.toReach5, ?_⟩
  rw [size_oneTerm4] at hc
  unfold costB5
  rw [lostB5_of_eq (ha.trans hb.symm)]
  omega

/-- **Fewest changes, `bra` asserted to begin with.** -/
theorem fewest_changes5_B {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach5 givenB4 g n ∧ n + 4 = costB5 g) ∧ ∀ n, Reach5 givenB4 g n → costB5 g ≤ n + 4 :=
  ⟨hb.elim (fewest_changes5_upper_B_apart hg hgw ha) (fewest_changes5_upper_B_merged hg hgw ha),
    fun _ h => fewest_changes5_lower_B h⟩

/-! ## What survives of the fourth derivation's cost -/

theorem lostA5_eq_zero_of_contains {g : MSt} (h : Contains4 givenA4 g) : lostA5 g = 0 := by
  have hm := h.mult (0, 1)
  rw [givenA4_arb] at hm
  rw [lostA5_of_ne (by rw [h.name_a, h.name_b, givenA4_a, givenA4_b]; omega), h.name_a, h.name_b,
    givenA4_a, givenA4_b]
  exact miss5_of_ne_zero (by omega)

theorem lostB5_eq_zero_of_contains {g : MSt} (h : Contains4 givenB4 g) : lostB5 g = 0 := by
  have h1 := h.mult (0, 1)
  have h2 := h.mult (1, 0)
  rw [givenB4_arb] at h1
  rw [givenB4_bra] at h2
  rw [lostB5_of_ne (by rw [h.name_a, h.name_b, givenB4_a, givenB4_b]; omega), h.name_a, h.name_b,
    givenB4_a, givenB4_b]
  rw [miss5_of_ne_zero (by omega), miss5_of_ne_zero (by omega)]

/-- On a state containing what is given, the fewest changes is the size difference — the
fourth derivation's cost survives on the fourth's results. -/
theorem fewest_changes5_of_contains_A {g : MSt} (hg : g.Legal) (hgw : g.WF)
    (h : Contains4 givenA4 g) :
    (∃ n, Reach5 givenA4 g n ∧ n + 3 = g.size) ∧ ∀ n, Reach5 givenA4 g n → g.size ≤ n + 3 := by
  constructor
  · obtain ⟨n, hn, hc⟩ := reach4_of_contains givenA4_wf hg hgw h
    rw [size_givenA4] at hc
    exact ⟨n, hn.toReach5, hc⟩
  · intro n hn
    have := fewest_changes5_lower_A hn
    unfold costA5 at this
    rw [lostA5_eq_zero_of_contains h] at this
    omega

theorem fewest_changes5_of_contains_B {g : MSt} (hg : g.Legal) (hgw : g.WF)
    (h : Contains4 givenB4 g) :
    (∃ n, Reach5 givenB4 g n ∧ n + 4 = g.size) ∧ ∀ n, Reach5 givenB4 g n → g.size ≤ n + 4 := by
  constructor
  · obtain ⟨n, hn, hc⟩ := reach4_of_contains givenB4_wf hg hgw h
    rw [size_givenB4] at hc
    exact ⟨n, hn.toReach5, hc⟩
  · intro n hn
    have := fewest_changes5_lower_B hn
    unfold costB5 at this
    rw [lostB5_eq_zero_of_contains h] at this
    omega

/-- The size can fall along a change: the fourth derivation's "size rises by exactly one"
and "cost = size difference" do not survive removal.  Removing `arb` from what is given
is one change to a state of size two, while the size difference is `−1`. -/
theorem size_can_fall : Reach5 givenA4 (givenA4.remove 0 1) 1 ∧ (givenA4.remove 0 1).size + 1 = givenA4.size :=
  ⟨Reach5.single step_remove_arb, by rw [size_removed_arb, size_givenA4]⟩

/-- The multiplicity of `arb` can fall to zero: no multiplicity is kept. -/
theorem arb_removed : Step5 givenA4 (givenA4.remove 0 1) ∧ (givenA4.remove 0 1).M (0, 1) = 0 :=
  ⟨step_remove_arb, by rw [remove_M_self, givenA4_arb]⟩

/-- The fourth derivation's containment does not survive: a state is not always
contained in its outcome. -/
theorem contains_fails : ¬ Contains4 givenA4 (givenA4.remove 0 1) := by
  intro h
  have := h.mult (0, 1)
  rw [remove_M_self, givenA4_arb] at this
  omega

end Seed.Fifth
