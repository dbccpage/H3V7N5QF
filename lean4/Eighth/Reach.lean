import Eighth.Cost

/-!
# Reachability with two relations: the names on the `r` part decide

Derived here:
* **clearing `s`**: every `s` assertion can be removed (`reach8_clear_s`), which
  leaves the embedding of the `r` part;
* **the criterion survives**: a well-formed two-relation state `g` is reachable
  from a well-formed `s` exactly when the names, if one term in `s`, are one
  term in `g` (`reach8_iff`) — the sixth's `reach6_iff` on the `r` part: clear
  `s`, follow the sixth's path on the `r` part with nothing in `s`
  (`Reach6.ofR`), add the target's `s` assertions (`reach8_from_ofR`); the `s`
  parts impose nothing (`reach8_iff_r`);
* **the results are every well-formed two-relation state** (`result8_iff_A`,
  `_B`), and any well-formed `r` part and `s` part on the same terms and names
  make a result (`results_pair`): the results are jointly free;
* reachability is mutual within the two classes (`reach8_symm`), one-way
  between them (`merged_never_apart8`), any two results are comparable
  (`reach8_total`), every result reaches itself in two changes (`cycle2_8`), so
  the lengths of the sequences reaching it are unbounded (`Reach8.unbounded`);
* the sixth's refutations of one-way reachability survive through the
  embedding (`no_return_fails8`, `antisymm_fails8`, `length_not_unique8`).
-/

namespace Seed.Eighth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth DSt

/-! ## Clearing the `s` relation -/

/-- Removing every `s` assertion, one at a time: the sixth's `reach5_clear` on the `s` part. -/
theorem reach8_clear_s : ∀ (d : ℕ) (s : DSt), s.WF → (s.proj true).total = d →
    Reach8 s (s.proj false).ofR d := by
  intro d
  induction d with
  | zero =>
    intro s hw h0
    have hz : s.NothingInS := by
      intro p
      unfold MSt.total at h0
      simp only [proj_T, proj_M] at h0
      by_cases hp : p ∈ s.T ×ˢ s.T
      · exact (Finset.sum_eq_zero_iff.1 h0) p hp
      · by_contra h
        exact hp (Finset.mem_product.2 (hw.2.1 p h))
    rw [← eq_ofR_of_nothing_in_s hz]
    exact Reach8.refl s
  | succ d ih =>
    intro s hw hd
    have hne : (s.proj true).total ≠ 0 := by omega
    unfold MSt.total at hne
    simp only [proj_T, proj_M] at hne
    obtain ⟨⟨x, y⟩, hq, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hxy : x ∈ s.T ∧ y ∈ s.T := Finset.mem_product.1 hq
    have st : Step8 s (s.remove true x y) := Step8.remove s true x y hp
    have ht : ((s.remove true x y).proj true).total = d := by
      rw [proj_remove_self]
      have := Seed.Fifth.total_remove (s.proj true) hxy.1 hxy.2 hp
      omega
    have r := ih (s.remove true x y) (st.wf hw) ht
    rw [proj_remove_other s (by decide) x y] at r
    have := (Reach8.single st).trans r
    rwa [Nat.add_comm] at this

/-! ## The criterion -/

/-- **Sufficiency.**  Clear `s`; the sixth's path on the `r` part with nothing in `s`; add the
target's `s` assertions. -/
theorem reach8_of_names {s g : DSt} (hs : s.WF) (hgw : g.WF) (h : s.a = s.b → g.a = g.b) :
    ∃ n, Reach8 s g n := by
  have r1 := reach8_clear_s _ s hs rfl
  obtain ⟨m, r2⟩ := reach6_of_names hs.1 hgw.1 h
  have r3 := reach8_from_ofR hgw
  exact ⟨_, (r1.trans r2.ofR).trans r3⟩

/-- **Reachability is decided by the names of the `r` part.** -/
theorem reach8_iff {s g : DSt} (hs : s.WF) (hgw : g.WF) :
    (∃ n, Reach8 s g n) ↔ (s.a = s.b → g.a = g.b) :=
  ⟨fun ⟨_, h⟩ hab => h.names_stay_merged hab, reach8_of_names hs hgw⟩

/-- The `s` parts impose nothing: reachability of two-relation states is reachability of their
`r` parts under the sixth seed. -/
theorem reach8_iff_r {s g : DSt} (hs : s.WF) (hgw : g.WF) :
    (∃ n, Reach8 s g n) ↔ ∃ n, Reach6 (s.proj false) (g.proj false) n := by
  rw [reach8_iff hs hgw, reach6_iff hs.1 hgw.1]
  rfl

/-- **The results, `bra` not asserted to begin with:** every well-formed two-relation state. -/
theorem result8_iff_A (g : DSt) : (∃ n, Reach8 givenA8 g n) ↔ g.WF :=
  ⟨fun ⟨_, h⟩ => h.wf givenA8_wf,
    fun hgw => reach8_of_names givenA8_wf hgw (fun h => absurd h (by rw [givenA8_a, givenA8_b]; omega))⟩

theorem result8_iff_B (g : DSt) : (∃ n, Reach8 givenB8 g n) ↔ g.WF :=
  ⟨fun ⟨_, h⟩ => h.wf givenB8_wf,
    fun hgw => reach8_of_names givenB8_wf hgw (fun h => absurd h (by rw [givenB8_a, givenB8_b]; omega))⟩

/-- **The results are jointly free**: any well-formed `r` part and `s` part on the same terms and
names make a result. -/
theorem results_pair {m m' : MSt} (hm : m.WF) (hm' : m'.WF) (hT : m'.T = m.T) (ha : m'.a = m.a)
    (hb : m'.b = m.b) :
    ∃ n, Reach8 givenA8 ⟨m.T, fun q => match q with | false => m.M | true => m'.M, m.a, m.b⟩ n := by
  apply (result8_iff_A _).2
  refine ⟨hm, ?_⟩
  show (⟨m.T, m'.M, m.a, m.b⟩ : MSt).WF
  rw [← hT, ← ha, ← hb]
  exact hm'

/-- A state asserting some `xsy` is a result: `asb` added to what is given, one change. -/
theorem s_is_a_result : Reach8 givenA8 (givenA8.addAssertion true 0 1) 1 ∧
    ¬ (givenA8.addAssertion true 0 1).NothingInS := by
  refine ⟨Reach8.single (Step8.addAssertion _ true 0 1 ((mem_givenA4_T 0).2 (Or.inl rfl))
    ((mem_givenA4_T 1).2 (Or.inr rfl))), fun h => ?_⟩
  have := h (0, 1)
  simp [DSt.addAssertion, givenA8, MSt.ofR] at this

/-- Reachability is mutual within the two classes. -/
theorem reach8_symm {s g : DSt} (hsw : s.WF) (hgw : g.WF) (h : g.a = g.b → s.a = s.b) :
    ∃ n, Reach8 g s n :=
  reach8_of_names hgw hsw h

/-- Every result with `a` and `b` two terms reaches what is given. -/
theorem reach8_back_A {g : DSt} (hgw : g.WF) (hne : g.a ≠ g.b) : ∃ n, Reach8 g givenA8 n :=
  reach8_of_names hgw givenA8_wf (fun h => absurd h hne)

/-- Any two results are comparable. -/
theorem reach8_total {s g : DSt} (hsw : s.WF) (hgw : g.WF) :
    (∃ n, Reach8 s g n) ∨ ∃ n, Reach8 g s n := by
  by_cases hab : s.a = s.b
  · by_cases hgab : g.a = g.b
    · exact Or.inl (reach8_of_names hsw hgw (fun _ => hgab))
    · exact Or.inr (reach8_of_names hgw hsw (fun h => absurd h hgab))
  · exact Or.inl (reach8_of_names hsw hgw (fun h => absurd h hab))

/-- One-way between the classes: from the one-term state what is given is never reached. -/
theorem merged_never_apart8 (n : ℕ) : ¬ Reach8 oneTerm4.ofR givenA8 n := by
  intro h
  have := h.names_stay_merged rfl
  rw [givenA8_a, givenA8_b] at this
  omega

/-! ## Every result reaches itself in two changes -/

/-- Adding an assertion and removing it again gives the state back. -/
theorem remove_addAssertion (s : DSt) (q : Rel) (x y : ℕ) : (s.addAssertion q x y).remove q x y = s := by
  apply ext_proj
  intro q'
  by_cases hq : q' = q
  · subst hq
    rw [proj_remove_self, proj_addAssertion_self]
    apply MSt.ext
    · rfl
    · funext p
      simp only [MSt.remove, MSt.addAssertion, Function.update_apply]
      split_ifs with hp <;> simp_all
    · rfl
    · rfl
  · rw [proj_remove_other _ hq, proj_addAssertion_other s hq]

theorem cycle2_8 {s : DSt} (hne : s.T.Nonempty) : Reach8 s s 2 := by
  obtain ⟨c, hc⟩ := hne
  have st1 : Step8 s (s.addAssertion false c c) := Step8.addAssertion s false c c hc hc
  have st2 : Step8 (s.addAssertion false c c) ((s.addAssertion false c c).remove false c c) :=
    Step8.remove _ false c c (by simp [DSt.addAssertion])
  rw [remove_addAssertion] at st2
  exact (Reach8.single st1).step st2

theorem Reach8.cycles {s : DSt} (hne : s.T.Nonempty) (k : ℕ) : Reach8 s s (2 * k) := by
  induction k with
  | zero => exact Reach8.refl s
  | succ k ih =>
    have := ih.trans (cycle2_8 hne)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact this

theorem Reach8.unbounded {s t : DSt} {n : ℕ} (h : Reach8 s t n) (hne : s.T.Nonempty) (k : ℕ) :
    Reach8 s t (2 * k + n) :=
  (Reach8.cycles hne k).trans h

/-! ## One-way reachability stays refuted -/

theorem no_return_fails8 : Reach8 givenA8 givenB8 1 ∧ Reach8 givenB8 givenA8 1 :=
  ⟨no_return_fails6.1.ofR, no_return_fails6.2.ofR⟩

theorem antisymm_fails8 :
    givenA8 ≠ givenB8 ∧ (∃ n, Reach8 givenA8 givenB8 n) ∧ ∃ m, Reach8 givenB8 givenA8 m := by
  refine ⟨fun h => antisymm_fails.1 ?_, ⟨1, no_return_fails8.1⟩, ⟨1, no_return_fails8.2⟩⟩
  have := congrArg (fun s : DSt => s.proj false) h
  exact this

theorem length_not_unique8 : Reach8 givenA8 givenA8 0 ∧ Reach8 givenA8 givenA8 2 :=
  ⟨Reach8.refl _, no_return_fails8.1.trans no_return_fails8.2⟩

end Seed.Eighth
