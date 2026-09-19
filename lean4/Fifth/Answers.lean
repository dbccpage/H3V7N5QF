import Fifth.Reach

/-!
# Attempts, obstructions and answers under the fifth seed

An *attempt* (`Try5`) is what the seed says to attempt: the four kinds without the
preconditions that make them unobstructed.  Derived here:
* an attempt is obstructed exactly when it adds some `xrx` or identifies two related
  terms (`Try5.obstructed_iff`); an unobstructed attempt is a performed change
  (`Try5.legal_iff`); removal and adding a term are never obstructed
  (`remove_legal`, `addTerm_unobstructed4`); adding an asserted `xry`, `x ≠ y`, is
  not obstructed (the fourth's `addAssertion_again_unobstructed`);
* an obstruction of an identification persists through every change but the
  removal of the obstructing assertion (`obstruction_persists5`, the first
  derivation's `obstruction_persists` with multiplicities);
* the answer "remove the obstruction" to an obstructed identification is a sequence
  of performed changes — lower `urv` and `vru` to zero, then identify — of length
  `M(u,v) + M(v,u) + 1` (`reach5_lower`, `remove_answer5`), and removing first or
  identifying first and then lowering the `uru` that results give the same state
  (`remove_obstruction_first_or_last5`);
* the builds for an obstructed `xrx` are the fourth derivation's two additions
  (`build_answer5`, `build_answer5_reverse`); that identifying the added term back
  with `x` gives exactly the would-be outcome is the fourth derivation's reading of
  a build, checked by computation (`is_build_of`) and, on supports, by the first
  derivation's `build_gives_back`;
* so every answer is a sequence of performed changes, and answers reach nothing the
  changes do not.
-/

namespace Seed.Fifth

open Seed Seed.Fourth MSt

/-- One attempted change of the fifth seed. -/
inductive Try5 : MSt → MSt → Prop
  | addTerm (s : MSt) (t : ℕ) (ht : t ∉ s.T) : Try5 s (s.addTerm t)
  | addAssertion (s : MSt) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Try5 s (s.addAssertion x y)
  | remove (s : MSt) (x y : ℕ) (hp : s.M (x, y) ≠ 0) : Try5 s (s.remove x y)
  | identify (s : MSt) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) : Try5 s (s.identify u v)

/-- Every performed change is an attempt. -/
theorem Step5.toTry5 {s t : MSt} (h : Step5 s t) : Try5 s t := by
  cases h with
  | addTerm t ht => exact Try5.addTerm s t ht
  | addAssertion x y hx hy hxy => exact Try5.addAssertion s x y hx hy
  | remove x y hp => exact Try5.remove s x y hp
  | identify u v hu hv huv h1 h2 => exact Try5.identify s u v hu hv huv

/-- An attempt is a performed change, or it adds some `xrx`, or it identifies two
related terms. -/
theorem Try5.step5_or_obstructed {s t : MSt} (h : Try5 s t) :
    Step5 s t ∨ (∃ x ∈ s.T, t = s.addAssertion x x) ∨
      ∃ u v, u ∈ s.T ∧ v ∈ s.T ∧ u ≠ v ∧ (s.M (u, v) ≠ 0 ∨ s.M (v, u) ≠ 0) ∧ t = s.identify u v := by
  cases h with
  | addTerm t ht => exact Or.inl (Step5.addTerm s t ht)
  | addAssertion x y hx hy =>
    by_cases hxy : x = y
    · subst hxy
      exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
    · exact Or.inl (Step5.addAssertion s x y hx hy hxy)
  | remove x y hp => exact Or.inl (Step5.remove s x y hp)
  | identify u v hu hv huv =>
    by_cases h1 : s.M (u, v) = 0
    · by_cases h2 : s.M (v, u) = 0
      · exact Or.inl (Step5.identify s u v hu hv huv h1 h2)
      · exact Or.inr (Or.inr ⟨u, v, hu, hv, huv, Or.inr h2, rfl⟩)
    · exact Or.inr (Or.inr ⟨u, v, hu, hv, huv, Or.inl h1, rfl⟩)

/-- **Which attempts are obstructed.**  On a legal state an attempt makes some `xrx`
asserted exactly when it adds some `xrx` or identifies two related terms. -/
theorem Try5.obstructed_iff {s t : MSt} (h : Try5 s t) (hs : s.Legal) :
    ¬ t.Legal ↔ (∃ x ∈ s.T, t = s.addAssertion x x) ∨
      ∃ u v, u ∈ s.T ∧ v ∈ s.T ∧ u ≠ v ∧ (s.M (u, v) ≠ 0 ∨ s.M (v, u) ≠ 0) ∧ t = s.identify u v := by
  constructor
  · intro ht
    rcases h.step5_or_obstructed with h5 | rest
    · exact absurd (h5.legal hs) ht
    · exact rest
  · rintro (⟨x, _, rfl⟩ | ⟨u, v, hu, hv, huv, hrel, rfl⟩)
    · exact adding_xrx_always_obstructed4 s x
    · intro hl
      obtain ⟨h1, h2⟩ := (identify_legal_iff hs hu hv huv).1 hl
      rcases hrel with h | h
      · exact h h1
      · exact h h2

/-- An unobstructed attempt is exactly a performed change. -/
theorem Try5.legal_iff {s t : MSt} (h : Try5 s t) (hs : s.Legal) : t.Legal ↔ Step5 s t := by
  constructor
  · intro ht
    rcases h.step5_or_obstructed with h5 | ⟨x, _, rfl⟩ | ⟨u, v, hu, hv, huv, hrel, rfl⟩
    · exact h5
    · exact absurd ht (adding_xrx_always_obstructed4 s x)
    · obtain ⟨h1, h2⟩ := (identify_legal_iff hs hu hv huv).1 ht
      rcases hrel with h | h
      · exact absurd h1 h
      · exact absurd h2 h
  · intro h5
    exact h5.legal hs

/-! ## An obstruction of an identification persists until it is removed -/

/-- **Persistence.**  If `urv` is asserted, then after any one performed change either
that change was a removal of `urv`, or `urv` is still asserted, or the change was an
identification and the assertion between the replaced terms is asserted. -/
theorem obstruction_persists5 {s t : MSt} (h : Step5 s t) (hw : s.WF) {u v : ℕ}
    (huv : s.M (u, v) ≠ 0) :
    t = s.remove u v ∨ t.M (u, v) ≠ 0 ∨
      ∃ p q, t = s.identify p q ∧ t.M (merge p q u, merge p q v) ≠ 0 := by
  have hmem : u ∈ s.T ∧ v ∈ s.T := hw.1 (u, v) huv
  cases h with
  | addTerm t ht => exact Or.inr (Or.inl huv)
  | addAssertion x y hx hy hxy =>
    refine Or.inr (Or.inl ?_)
    have := (Step4.addAssertion s x y hx hy hxy).contains.mult (u, v)
    omega
  | remove x y hp =>
    by_cases he : (x, y) = (u, v)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact Or.inl rfl
    · refine Or.inr (Or.inl ?_)
      rw [remove_M_of_ne s x y (Ne.symm he)]
      exact huv
  | identify p q hp hq hpq h1 h2 =>
    refine Or.inr (Or.inr ⟨p, q, rfl, ?_⟩)
    have := identify_M_ge s p q hmem.1 hmem.2
    omega

/-! ## The answer "remove the obstruction" -/

/-- The state with the multiplicity of `p` lowered to zero. -/
def lowered (s : MSt) (p : ℕ × ℕ) : MSt := ⟨s.T, Function.update s.M p 0, s.a, s.b⟩

/-- Lowering one multiplicity to zero, one removal per unit. -/
theorem reach5_lower : ∀ (k : ℕ) (s : MSt) (x y : ℕ), s.M (x, y) = k →
    Reach5 s (lowered s (x, y)) k := by
  intro k
  induction k with
  | zero =>
    intro s x y h0
    have e : lowered s (x, y) = s := by
      apply MSt.ext
      · rfl
      · show Function.update s.M (x, y) 0 = s.M
        have := Function.update_eq_self (x, y) s.M
        rw [h0] at this
        exact this
      · rfl
      · rfl
    rw [e]
    exact Reach5.refl s
  | succ k ih =>
    intro s x y hk
    have st : Step5 s (s.remove x y) := Step5.remove s x y (by omega)
    have r := ih (s.remove x y) x y (by rw [remove_M_self, hk]; omega)
    have e : lowered (s.remove x y) (x, y) = lowered s (x, y) := by
      apply MSt.ext
      · rfl
      · show Function.update (Function.update s.M (x, y) (s.M (x, y) - 1)) (x, y) 0 =
          Function.update s.M (x, y) 0
        exact Function.update_idem _ _ _
      · rfl
      · rfl
    rw [e] at r
    have := (Reach5.single st).trans r
    rwa [Nat.add_comm] at this

theorem lowered_M_of_ne (s : MSt) {p q : ℕ × ℕ} (h : q ≠ p) : (lowered s p).M q = s.M q :=
  Function.update_of_ne h _ _

theorem lowered_M_self (s : MSt) (p : ℕ × ℕ) : (lowered s p).M p = 0 :=
  Function.update_self _ _ _

/-- **The answer "remove the obstruction"** to an identification of `u` and `v`: lower
`urv` and `vru` to zero, then identify — a sequence of `M(u,v) + M(v,u) + 1` performed
changes.  (Where only one of them is asserted, the other lowering is zero changes.) -/
theorem remove_answer5 (s : MSt) {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
    Reach5 s ((lowered (lowered s (u, v)) (v, u)).identify u v) (s.M (u, v) + s.M (v, u) + 1) := by
  have hne : ((v, u) : ℕ × ℕ) ≠ (u, v) := fun h => huv (Prod.mk.inj h).1.symm
  have r1 := reach5_lower _ s u v rfl
  have r2 := reach5_lower _ (lowered s (u, v)) v u rfl
  rw [lowered_M_of_ne s hne] at r2
  have st : Step5 (lowered (lowered s (u, v)) (v, u)) ((lowered (lowered s (u, v)) (v, u)).identify u v) :=
    Step5.identify _ u v hu hv huv
      (by rw [lowered_M_of_ne _ hne.symm, lowered_M_self]) (lowered_M_self _ _)
  exact (r1.trans r2).step st

/-- Removing the obstruction first, or identifying and then lowering the `uru` that
results to zero: the same state (the first derivation's
`remove_obstruction_first_or_last`, with multiplicities). -/
theorem remove_obstruction_first_or_last5 {s : MSt} (hs : s.Legal) {u v : ℕ} (huv : u ≠ v) :
    (lowered (lowered s (u, v)) (v, u)).identify u v = lowered (s.identify u v) (u, u) := by
  apply MSt.ext
  · rfl
  · funext p
    show ∑ q ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = p),
        Function.update (Function.update s.M (u, v) 0) (v, u) 0 q =
      Function.update (s.identify u v).M (u, u) 0 p
    rw [Function.update_apply]
    split_ifs with hp
    · subst hp
      apply Finset.sum_eq_zero
      rintro ⟨x, y⟩ hq
      obtain ⟨_, hxy⟩ := mem_fiber.1 hq
      simp only [Prod.mk.injEq, merge_eq_left_iff] at hxy
      simp only [Function.update_apply]
      split_ifs with h1 h2
      · rfl
      · rfl
      · have hxy' : x = y := by
          rcases hxy with ⟨hx | hx, hy | hy⟩ <;> simp_all
        rw [hxy']
        exact hs y
    · rw [identify_M]
      apply Finset.sum_congr rfl
      rintro ⟨x, y⟩ hq
      obtain ⟨_, hxy⟩ := mem_fiber.1 hq
      have h1 : ((x, y) : ℕ × ℕ) ≠ (u, v) := by
        rintro ⟨⟩
        apply hp
        rw [← hxy]
        simp
      have h2 : ((x, y) : ℕ × ℕ) ≠ (v, u) := by
        rintro ⟨⟩
        apply hp
        rw [← hxy]
        simp
      rw [Function.update_of_ne h2, Function.update_of_ne h1]
  · rfl
  · rfl

/-! ## Builds -/

/-- The build with fewest additions, `x r t` with `t` new, is two performed changes (the
fourth derivation's, through the embedding). -/
theorem build_answer5 {s : MSt} {x t : ℕ} (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach5 s ((s.addTerm t).addAssertion x t) 2 :=
  (build_answer4 hx ht).toReach5

theorem build_answer5_reverse {s : MSt} {x t : ℕ} (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach5 s ((s.addTerm t).addAssertion t x) 2 :=
  (build_answer4_reverse hx ht).toReach5

end Seed.Fifth
