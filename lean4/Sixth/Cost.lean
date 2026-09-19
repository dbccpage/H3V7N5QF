import Sixth.Step

/-!
# Fewest changes under the sixth seed

The potential is the fifth's, `size + 2 · lost`, with one change in `lost`: when
the names are one term `c`, the destroyed givens are `m0 + 1 − min(M(c,c), m0)` —
the merge itself, plus the given assertions the merge did not carry into `crc` —
instead of the fifth's `m0 + 1` (which assumed `crc` could not be asserted).
With the names apart, `lost` is the fifth's (the givens at multiplicity zero).

Derived here:
* one change raises the potential by at most one (`Step6.costA_le`,
  `Step6.costB_le`); the identification of `a` with `b` no longer needs nothing
  asserted between them, since the outcome asserts `crc` at least
  `M(a,b) + M(b,a)` times (`identify_M_ge_pair`); so a state reached from what
  is given in `n` changes has cost at most `n` plus the cost of what is given
  (`fewest_changes6_lower_A`, `_B`);
* additions reach every well-formed state containing a well-formed state, `xrx`
  added like any pair (`reach6_by_additions`, `reach6_of_contains` — the fourth's
  proof without its legality hypothesis);
* the bound is attained: names apart, remove the missing givens then add; names
  one term, remove `m0 − min(M(0,0), m0)` givens, identify, then add from the
  one-term state asserting `0r0` `min(M(0,0), m0)` times (`fewest_changes6_A`,
  `fewest_changes6_B`);
* on states asserting no `xrx` the destroyed givens are the fifth's
  (`lostA6_eq_lostA5_of_legal`), so the fifth's fewest changes survive there
  (`fewest_changes6_of_legal_A`, `_B`) and on every state with the names apart
  (`lostA6_of_ne`); they fail elsewhere: identifying `a` and `b` in what is given
  is one change where the fifth's potential rises by three
  (`fifth_potential_fails`);
* on states containing what is given the fewest changes is the size difference
  (`fewest_changes6_of_contains_A`, `_B`), as under the fourth and fifth seeds;
* every change moves the size by exactly one either way (`Step6.size_step`,
  `Reach6.size_parity`): the fifth's parity survives.

Cited from the fifth derivation and re-checked: `miss5`, `lostA5`, `lostB5`,
`costA5`, `costB5` are the fifth's definitions; the removal paths from what is
given (`step_remove_arb`, `removed_arb_contains`, `givenA4_to_oneTerm4`,
`givenB4_to_oneTerm4`, `givenB4_remove_bra_eq`, the four `givenB4_remove_…`
containments) mention no legality of the *target* and are used through the
embedding.  From the fourth: `size_addTerm`, `size_addAssertion` (no `x ≠ y`
needed), `Contains4`, `givenA4_contains`, `givenB4_contains`, `total_widen`.
-/

namespace Seed.Sixth

open Seed Seed.Fourth Seed.Fifth MSt

/-- Destroyed givens, `bra` not given: with the names one term, the merge plus the given
`arb` unless it survives as `ara`; with them apart, `arb` if it is not asserted. -/
def lostA6 (s : MSt) : ℕ := if s.a = s.b then 2 - min (s.M (s.a, s.a)) 1 else miss5 s s.a s.b

/-- Destroyed givens, `bra` given. -/
def lostB6 (s : MSt) : ℕ :=
  if s.a = s.b then 3 - min (s.M (s.a, s.a)) 2 else miss5 s s.a s.b + miss5 s s.b s.a

/-- Size (multiplicities counted) plus two for each destroyed given (`bra` not given). -/
def costA6 (s : MSt) : ℕ := s.size + 2 * lostA6 s

/-- Size plus two for each destroyed given (`bra` given). -/
def costB6 (s : MSt) : ℕ := s.size + 2 * lostB6 s

/-! ## The destroyed givens -/

theorem lostA6_of_eq {s : MSt} (h : s.a = s.b) : lostA6 s = 2 - min (s.M (s.a, s.a)) 1 := by
  simp [lostA6, h]

theorem lostA6_of_ne {s : MSt} (h : s.a ≠ s.b) : lostA6 s = miss5 s s.a s.b := by simp [lostA6, h]

theorem lostB6_of_eq {s : MSt} (h : s.a = s.b) : lostB6 s = 3 - min (s.M (s.a, s.a)) 2 := by
  simp [lostB6, h]

theorem lostB6_of_ne {s : MSt} (h : s.a ≠ s.b) : lostB6 s = miss5 s s.a s.b + miss5 s s.b s.a := by
  simp [lostB6, h]

/-- With the names apart the destroyed givens are the fifth's. -/
theorem lostA6_eq_lostA5_of_ne {s : MSt} (h : s.a ≠ s.b) : lostA6 s = lostA5 s := by
  rw [lostA6_of_ne h, lostA5_of_ne h]

theorem lostB6_eq_lostB5_of_ne {s : MSt} (h : s.a ≠ s.b) : lostB6 s = lostB5 s := by
  rw [lostB6_of_ne h, lostB5_of_ne h]

/-- On a state asserting no `xrx` the destroyed givens are the fifth's. -/
theorem lostA6_eq_lostA5_of_legal {s : MSt} (hs : s.Legal) : lostA6 s = lostA5 s := by
  by_cases h : s.a = s.b
  · rw [lostA6_of_eq h, lostA5_of_eq h, hs s.a]
    rfl
  · exact lostA6_eq_lostA5_of_ne h

theorem lostB6_eq_lostB5_of_legal {s : MSt} (hs : s.Legal) : lostB6 s = lostB5 s := by
  by_cases h : s.a = s.b
  · rw [lostB6_of_eq h, lostB5_of_eq h, hs s.a]
    rfl
  · exact lostB6_eq_lostB5_of_ne h

theorem costA6_eq_costA5_of_legal {s : MSt} (hs : s.Legal) : costA6 s = costA5 s := by
  unfold costA6 costA5
  rw [lostA6_eq_lostA5_of_legal hs]

theorem costB6_eq_costB5_of_legal {s : MSt} (hs : s.Legal) : costB6 s = costB5 s := by
  unfold costB6 costB5
  rw [lostB6_eq_lostB5_of_legal hs]

theorem lostA6_le_two (s : MSt) : lostA6 s ≤ 2 := by
  unfold lostA6
  split_ifs
  · omega
  · have := miss5_le_one s s.a s.b
    omega

theorem lostB6_le_three (s : MSt) : lostB6 s ≤ 3 := by
  unfold lostB6
  split_ifs
  · omega
  · have h1 := miss5_le_one s s.a s.b
    have h2 := miss5_le_one s s.b s.a
    omega

/-- An addition destroys nothing: its state is contained in its outcome. -/
theorem lostA6_le_of_contains {s t : MSt} (h : Contains4 s t) : lostA6 t ≤ lostA6 s := by
  unfold lostA6
  rw [h.name_a, h.name_b]
  split_ifs
  · have := h.mult (s.a, s.a)
    omega
  · exact miss5_le_of_le (h.mult _)

theorem lostB6_le_of_contains {s t : MSt} (h : Contains4 s t) : lostB6 t ≤ lostB6 s := by
  unfold lostB6
  rw [h.name_a, h.name_b]
  split_ifs
  · have := h.mult (s.a, s.a)
    omega
  · exact Nat.add_le_add (miss5_le_of_le (h.mult _)) (miss5_le_of_le (h.mult _))

/-- Adding any assertion, `xrx` included, leaves the state contained in its outcome
(the fourth's `Step4.contains` without `x ≠ y`). -/
theorem addAssertion_contains (s : MSt) (x y : ℕ) : Contains4 s (s.addAssertion x y) := by
  refine ⟨Finset.Subset.refl _, fun p => ?_, rfl, rfl⟩
  show s.M p ≤ Function.update s.M (x, y) (s.M (x, y) + 1) p
  rw [Function.update_apply]
  split_ifs with hp
  · subst hp
    omega
  · exact le_refl _

/-- A removal lowers one multiplicity by one, so it destroys at most one given. -/
theorem lostA6_remove (s : MSt) (x y : ℕ) : lostA6 (s.remove x y) ≤ lostA6 s + 1 := by
  by_cases h : s.a = s.b
  · rw [lostA6_of_eq (s := s.remove x y) h, lostA6_of_eq h, remove_a, remove_M, Function.update_apply]
    split_ifs <;> omega
  · rw [lostA6_of_ne (s := s.remove x y) h, lostA6_of_ne h, remove_a, remove_b]
    exact miss5_remove_le s x y s.a s.b

theorem lostB6_remove (s : MSt) (x y : ℕ) : lostB6 (s.remove x y) ≤ lostB6 s + 1 := by
  by_cases h : s.a = s.b
  · rw [lostB6_of_eq (s := s.remove x y) h, lostB6_of_eq h, remove_a, remove_M, Function.update_apply]
    split_ifs with hxy
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
      subst h1 h2
      omega
    · omega
  · have := lostB5_remove s x y
    rwa [lostB6_eq_lostB5_of_ne (s := s.remove x y) h, lostB6_eq_lostB5_of_ne h]

/-- An identification destroys at most one given, whatever is asserted between the merged
terms: merging `a` and `b` carries `M(a,b) + M(b,a)` into `crc`. -/
theorem lostA6_identify {s : MSt} (hw : s.WF) {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
    lostA6 (s.identify u v) ≤ lostA6 s + 1 := by
  by_cases hab : s.a = s.b
  · have h' : (s.identify u v).a = (s.identify u v).b := by simp [hab]
    rw [lostA6_of_eq h', lostA6_of_eq hab, identify_a]
    have := identify_M_ge s u v hw.2.1 hw.2.1
    omega
  · by_cases hab' : (s.identify u v).a = (s.identify u v).b
    · rw [lostA6_of_eq hab', lostA6_of_ne hab, identify_a]
      simp only [identify_a, identify_b] at hab'
      have hpair := identify_M_ge_pair s hu hv huv
      rcases merge_eq_merge hab hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb, merge_left]
        unfold miss5
        split_ifs <;> omega
      · rw [ha, hb, merge_right]
        unfold miss5
        split_ifs <;> omega
    · rw [lostA6_of_ne hab', lostA6_of_ne hab]
      simp only [identify_a, identify_b]
      have e := miss5_le_of_le (identify_M_ge s u v hw.2.1 hw.2.2)
      omega

theorem lostB6_identify {s : MSt} (hw : s.WF) {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
    lostB6 (s.identify u v) ≤ lostB6 s + 1 := by
  by_cases hab : s.a = s.b
  · have h' : (s.identify u v).a = (s.identify u v).b := by simp [hab]
    rw [lostB6_of_eq h', lostB6_of_eq hab, identify_a]
    have := identify_M_ge s u v hw.2.1 hw.2.1
    omega
  · by_cases hab' : (s.identify u v).a = (s.identify u v).b
    · rw [lostB6_of_eq hab', lostB6_of_ne hab, identify_a]
      simp only [identify_a, identify_b] at hab'
      have hpair := identify_M_ge_pair s hu hv huv
      rcases merge_eq_merge hab hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb, merge_left]
        unfold miss5
        split_ifs <;> omega
      · rw [ha, hb, merge_right]
        unfold miss5
        split_ifs <;> omega
    · rw [lostB6_of_ne hab', lostB6_of_ne hab]
      simp only [identify_a, identify_b]
      have e1 := miss5_le_of_le (identify_M_ge s u v hw.2.1 hw.2.2)
      have e2 := miss5_le_of_le (identify_M_ge s u v hw.2.2 hw.2.1)
      omega

/-! ## One change raises the cost by at most one -/

theorem Step6.costA_le {s t : MSt} (h : Step6 s t) (hw : s.WF) : costA6 t ≤ costA6 s + 1 := by
  unfold costA6
  cases h with
  | addTerm t ht =>
    have e := Seed.Fourth.size_addTerm hw ht
    have l := lostA6_le_of_contains (Step4.addTerm s t ht).contains
    omega
  | addAssertion x y hx hy =>
    have e := Seed.Fourth.size_addAssertion hx hy
    have l := lostA6_le_of_contains (addAssertion_contains s x y)
    omega
  | remove x y hp =>
    have hxy : x ∈ s.T ∧ y ∈ s.T := hw.1 (x, y) hp
    have e := Seed.Fifth.size_remove s hxy.1 hxy.2 hp
    have l := lostA6_remove s x y
    omega
  | identify u v hu hv huv =>
    have e := Seed.Fifth.size_identify s hu hv huv
    have l := lostA6_identify hw hu hv huv
    omega

theorem Step6.costB_le {s t : MSt} (h : Step6 s t) (hw : s.WF) : costB6 t ≤ costB6 s + 1 := by
  unfold costB6
  cases h with
  | addTerm t ht =>
    have e := Seed.Fourth.size_addTerm hw ht
    have l := lostB6_le_of_contains (Step4.addTerm s t ht).contains
    omega
  | addAssertion x y hx hy =>
    have e := Seed.Fourth.size_addAssertion hx hy
    have l := lostB6_le_of_contains (addAssertion_contains s x y)
    omega
  | remove x y hp =>
    have hxy : x ∈ s.T ∧ y ∈ s.T := hw.1 (x, y) hp
    have e := Seed.Fifth.size_remove s hxy.1 hxy.2 hp
    have l := lostB6_remove s x y
    omega
  | identify u v hu hv huv =>
    have e := Seed.Fifth.size_identify s hu hv huv
    have l := lostB6_identify hw hu hv huv
    omega

theorem Reach6.costA_le {s t : MSt} {n : ℕ} (h : Reach6 s t n) (hw : s.WF) :
    costA6 t ≤ costA6 s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costA_le (r.wf hw)
    omega

theorem Reach6.costB_le {s t : MSt} {n : ℕ} (h : Reach6 s t n) (hw : s.WF) :
    costB6 t ≤ costB6 s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costB_le (r.wf hw)
    omega

/-! ## Every change moves the size by one: parity survives -/

theorem Step6.size_step {s t : MSt} (h : Step6 s t) (hw : s.WF) :
    t.size = s.size + 1 ∨ t.size + 1 = s.size := by
  cases h with
  | addTerm t ht => exact Or.inl (Seed.Fourth.size_addTerm hw ht)
  | addAssertion x y hx hy => exact Or.inl (Seed.Fourth.size_addAssertion hx hy)
  | remove x y hp =>
    have hxy : x ∈ s.T ∧ y ∈ s.T := hw.1 (x, y) hp
    exact Or.inr (Seed.Fifth.size_remove s hxy.1 hxy.2 hp)
  | identify u v hu hv huv => exact Or.inr (Seed.Fifth.size_identify s hu hv huv)

theorem Reach6.size_parity {s t : MSt} {n : ℕ} (h : Reach6 s t n) (hw : s.WF) :
    (s.size + t.size + n) % 2 = 0 := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step (r.wf hw) with e | e <;> omega

/-! ## What is given -/

theorem lostA6_givenA4 : lostA6 givenA4 = 0 := by
  rw [lostA6_eq_lostA5_of_legal givenA4_legal, lostA5_givenA4]

theorem lostB6_givenB4 : lostB6 givenB4 = 0 := by
  rw [lostB6_eq_lostB5_of_legal givenB4_legal, lostB5_givenB4]

theorem costA6_givenA4 : costA6 givenA4 = 3 := by
  rw [costA6, size_givenA4, lostA6_givenA4]

theorem costB6_givenB4 : costB6 givenB4 = 4 := by
  rw [costB6, size_givenB4, lostB6_givenB4]

/-- **Lower bound, `bra` not asserted to begin with.** -/
theorem fewest_changes6_lower_A {t : MSt} {n : ℕ} (h : Reach6 givenA4 t n) : costA6 t ≤ n + 3 := by
  have := h.costA_le givenA4_wf
  rw [costA6_givenA4] at this
  omega

/-- **Lower bound, `bra` asserted to begin with.** -/
theorem fewest_changes6_lower_B {t : MSt} {n : ℕ} (h : Reach6 givenB4 t n) : costB6 t ≤ n + 4 := by
  have := h.costB_le givenB4_wf
  rw [costB6_givenB4] at this
  omega

/-! ## Additions reach everything that contains the state (no legality needed) -/

theorem reach6_addTerms (s : MSt) (D : Finset ℕ) (hD : Disjoint D s.T) :
    Reach6 s ⟨s.T ∪ D, s.M, s.a, s.b⟩ D.card := by
  revert hD
  refine Finset.induction_on D ?_ ?_
  · intro _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach6.refl s
  · intro t D ht ih hD
    rw [Finset.disjoint_insert_left] at hD
    have r := ih hD.2
    have hnew : t ∉ s.T ∪ D := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hD.1, ht⟩
    have st := Step6.addTerm ⟨s.T ∪ D, s.M, s.a, s.b⟩ t hnew
    rw [Finset.card_insert_of_notMem ht, Finset.union_insert]
    exact Reach6.step r st

/-- Raising multiplicities one at a time, `xrx` like any pair. -/
theorem reach6_raise (g : MSt) (hgw : g.WF) :
    ∀ (d : ℕ) (s : MSt), s.T = g.T → s.a = g.a → s.b = g.b → s.WF → (∀ p, s.M p ≤ g.M p) →
      g.total = s.total + d → Reach6 s g d := by
  intro d
  induction d with
  | zero =>
    intro s hT ha hb hw hle htot
    have e : s = g := by
      apply MSt.ext
      · exact hT
      · funext p
        by_cases hp : p ∈ g.T ×ˢ g.T
        · by_contra hne
          have hlt : s.M p < g.M p := lt_of_le_of_ne (hle p) hne
          have : ∑ q ∈ g.T ×ˢ g.T, s.M q < ∑ q ∈ g.T ×ˢ g.T, g.M q :=
            Finset.sum_lt_sum (fun q _ => hle q) ⟨p, hp, hlt⟩
          unfold MSt.total at htot
          rw [hT] at htot
          omega
        · have h1 : g.M p = 0 := by
            by_contra h
            exact hp (Finset.mem_product.2 (hgw.1 p h))
          have h2 : s.M p = 0 := by
            by_contra h
            have := hw.1 p h
            rw [hT] at this
            exact hp (Finset.mem_product.2 this)
          rw [h1, h2]
      · exact ha
      · exact hb
    rw [e]
    exact Reach6.refl g
  | succ d ih =>
    intro s hT ha hb hw hle htot
    have hlt : ∑ q ∈ g.T ×ˢ g.T, s.M q < ∑ q ∈ g.T ×ˢ g.T, g.M q := by
      unfold MSt.total at htot
      rw [hT] at htot
      omega
    obtain ⟨p, hp, hplt⟩ := Finset.exists_lt_of_sum_lt hlt
    obtain ⟨x, y⟩ := p
    have hxT : x ∈ s.T := by rw [hT]; exact (Finset.mem_product.1 hp).1
    have hyT : y ∈ s.T := by rw [hT]; exact (Finset.mem_product.1 hp).2
    have st := Step6.addAssertion s x y hxT hyT
    have hw' := st.wf hw
    have hle' : ∀ q, (s.addAssertion x y).M q ≤ g.M q := by
      intro q
      show Function.update s.M (x, y) (s.M (x, y) + 1) q ≤ g.M q
      rw [Function.update_apply]
      split_ifs with hq
      · subst hq
        omega
      · exact hle q
    have htot' : g.total = (s.addAssertion x y).total + d := by
      rw [total_addAssertion hxT hyT]
      omega
    have r := ih (s.addAssertion x y) hT ha hb hw' hle' htot'
    have : Reach6 s g (1 + d) := Reach6.trans (Reach6.step (Reach6.refl s) st) r
    rw [Nat.add_comm] at this
    exact this

/-- **Additions reach everything that contains the state.** -/
theorem reach6_by_additions (s g : MSt) (hs : s.WF) (hgw : g.WF) (h : Contains4 s g) :
    Reach6 s g ((g.T \ s.T).card + (g.total - s.total)) := by
  have r1 := reach6_addTerms s (g.T \ s.T) Finset.sdiff_disjoint
  have hTT : s.T ∪ g.T \ s.T = g.T := Finset.union_sdiff_of_subset h.terms
  rw [hTT] at r1
  have hw1 : (⟨g.T, s.M, s.a, s.b⟩ : MSt).WF :=
    ⟨fun p hp => ⟨h.terms (hs.1 p hp).1, h.terms (hs.1 p hp).2⟩, h.terms hs.2.1, h.terms hs.2.2⟩
  have htot1 : (⟨g.T, s.M, s.a, s.b⟩ : MSt).total = s.total := total_widen hs h.terms
  have hle := h.total_le
  have r2 := reach6_raise g hgw (g.total - s.total) ⟨g.T, s.M, s.a, s.b⟩ rfl h.name_a.symm
    h.name_b.symm hw1 h.mult (by rw [htot1]; omega)
  exact r1.trans r2

/-- A well-formed state that contains `s` is reached from `s` in exactly the size
difference (the fourth's `reach4_of_contains` without legality). -/
theorem reach6_of_contains {s g : MSt} (hs : s.WF) (hgw : g.WF) (h : Contains4 s g) :
    ∃ n, Reach6 s g n ∧ n + s.size = g.size := by
  refine ⟨_, reach6_by_additions s g hs hgw h, ?_⟩
  have hc := Finset.card_sdiff_add_card_eq_card h.terms
  have hle := h.total_le
  unfold MSt.size
  omega

/-! ## Upper bound, `bra` not given -/

/-- **Names apart.**  Remove `arb` if the target lacks it, then add. -/
theorem fewest_changes6_upper_A_apart {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1) :
    ∃ n, Reach6 givenA4 g n ∧ n + 3 = costA6 g := by
  have hne : g.a ≠ g.b := by rw [ha, hb]; omega
  by_cases hab : g.M (0, 1) = 0
  · have hw1 : (givenA4.remove 0 1).WF := step_remove_arb.wf givenA4_wf
    obtain ⟨n, hn, hc⟩ := reach6_of_contains hw1 hgw (removed_arb_contains hgw ha hb)
    refine ⟨1 + n, (Reach6.single step_remove_arb.toStep6).trans hn, ?_⟩
    rw [size_removed_arb] at hc
    unfold costA6
    rw [lostA6_of_ne hne, miss5_of_zero (by rw [ha, hb]; exact hab)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains givenA4_wf hgw (givenA4_contains hgw ha hb hab)
    refine ⟨n, hn, ?_⟩
    rw [size_givenA4] at hc
    unfold costA6
    rw [lostA6_of_ne hne, miss5_of_ne_zero (by rw [ha, hb]; exact hab)]
    omega

/-- The outcome of identifying `a` and `b` in what is given (`bra` not given): one term
asserting `0r0` once. -/
theorem identify_givenA4_eq : givenA4.identify 0 1 = loopState 1 := by
  have h0 : (0 : ℕ) ∈ givenA4.T := (mem_givenA4_T 0).2 (Or.inl rfl)
  have h1 : (1 : ℕ) ∈ givenA4.T := (mem_givenA4_T 1).2 (Or.inr rfl)
  have hall : ∀ x ∈ givenA4.T, merge 0 1 x = 0 := by
    intro x hx
    rcases (mem_givenA4_T x).1 hx with rfl | rfl
    · exact merge_left 0 1
    · exact merge_right 0 1
  have hle : (givenA4.identify 0 1).M (0, 0) ≤ 1 := by
    have htot := total_identify givenA4 (v := 1) h0 (by omega)
    have hgiven : givenA4.total = 1 := by decide
    have hmem : ((0, 0) : ℕ × ℕ) ∈ (givenA4.identify 0 1).T ×ˢ (givenA4.identify 0 1).T := by
      rw [identify_T]
      exact Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨by omega, h0⟩, Finset.mem_erase.2 ⟨by omega, h0⟩⟩
    have hsingle : (givenA4.identify 0 1).M (0, 0) ≤ (givenA4.identify 0 1).total := by
      unfold MSt.total
      exact Finset.single_le_sum (f := (givenA4.identify 0 1).M) (fun _ _ => Nat.zero_le _) hmem
    omega
  have hge := identify_M_ge_pair givenA4 h0 h1 (by omega)
  rw [givenA4_arb, givenA4_bra] at hge
  apply MSt.ext
  · show ({0, 1} : Finset ℕ).erase 1 = {0}
    decide
  · funext p
    by_cases hp : p = (0, 0)
    · subst hp
      rw [loopState_M_self]
      omega
    · rw [identify_M_eq_zero_of_all_merged givenA4 0 1 hall hp, loopState_M_of_ne 1 hp]
  · rfl
  · rfl

theorem step_identify_givenA4 : Step6 givenA4 (loopState 1) :=
  identify_givenA4_eq ▸ step_identify_given

/-- **Names one term.**  If the target asserts `0r0`, identify `a` and `b` at once (one
change, `ara` kept); otherwise remove `arb` first (the fifth's path to the one-term
state).  Then add. -/
theorem fewest_changes6_upper_A_merged {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 0) :
    ∃ n, Reach6 givenA4 g n ∧ n + 3 = costA6 g := by
  have heq : g.a = g.b := ha.trans hb.symm
  unfold costA6
  rw [lostA6_of_eq heq, ha]
  by_cases hk : g.M (0, 0) = 0
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains oneTerm4_wf hgw (oneTerm4_contains hgw ha hb)
    refine ⟨2 + n, givenA4_to_oneTerm4.toReach6.trans hn, ?_⟩
    rw [size_oneTerm4] at hc
    rw [hk]
    omega
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains (loopState_wf 1) hgw
      (loopState_contains hgw ha hb (by omega))
    refine ⟨1 + n, (Reach6.single step_identify_givenA4).trans hn, ?_⟩
    rw [size_loopState] at hc
    have : min (g.M (0, 0)) 1 = 1 := by omega
    rw [this]
    omega

/-- **Fewest changes, `bra` not asserted to begin with.**  A well-formed state written
with `a = 0` and `b ∈ {0, 1}` is reached in exactly `costA6 g − 3` changes and no
fewer. -/
theorem fewest_changes6_A {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach6 givenA4 g n ∧ n + 3 = costA6 g) ∧ ∀ n, Reach6 givenA4 g n → costA6 g ≤ n + 3 :=
  ⟨hb.elim (fewest_changes6_upper_A_apart hgw ha) (fewest_changes6_upper_A_merged hgw ha),
    fun _ h => fewest_changes6_lower_A h⟩

/-! ## Upper bound, `bra` given -/

/-- **Names apart.** -/
theorem fewest_changes6_upper_B_apart {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1) :
    ∃ n, Reach6 givenB4 g n ∧ n + 4 = costB6 g := by
  have hne : g.a ≠ g.b := by rw [ha, hb]; omega
  unfold costB6
  rw [lostB6_of_ne hne]
  by_cases hab : g.M (0, 1) = 0 <;> by_cases hba : g.M (1, 0) = 0
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains (step_remove_both_B.wf (step_remove_arb_B.wf givenB4_wf))
      hgw (givenB4_remove_both_contains hgw ha hb)
    refine ⟨2 + n, ((Reach6.single step_remove_arb_B.toStep6).step step_remove_both_B.toStep6).trans hn, ?_⟩
    rw [size_givenB4_remove_both] at hc
    rw [miss5_of_zero (by rw [ha, hb]; exact hab), miss5_of_zero (by rw [ha, hb]; exact hba)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains (step_remove_arb_B.wf givenB4_wf) hgw
      (givenB4_remove_arb_contains hgw ha hb hba)
    refine ⟨1 + n, (Reach6.single step_remove_arb_B.toStep6).trans hn, ?_⟩
    rw [size_givenB4_remove_arb] at hc
    rw [miss5_of_zero (by rw [ha, hb]; exact hab), miss5_of_ne_zero (by rw [ha, hb]; exact hba)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains (step_remove_bra_B.wf givenB4_wf) hgw
      (givenB4_remove_bra_contains hgw ha hb hab)
    refine ⟨1 + n, (Reach6.single step_remove_bra_B.toStep6).trans hn, ?_⟩
    rw [size_givenB4_remove_bra] at hc
    rw [miss5_of_ne_zero (by rw [ha, hb]; exact hab), miss5_of_zero (by rw [ha, hb]; exact hba)]
    omega
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains givenB4_wf hgw (givenB4_contains hgw ha hb hab hba)
    refine ⟨n, hn, ?_⟩
    rw [size_givenB4] at hc
    rw [miss5_of_ne_zero (by rw [ha, hb]; exact hab), miss5_of_ne_zero (by rw [ha, hb]; exact hba)]
    omega

/-- Identifying `a` and `b` in what is given with `bra`: one term asserting `0r0` twice. -/
theorem identify_givenB4_eq : givenB4.identify 0 1 = loopState 2 := by
  have h0 : (0 : ℕ) ∈ givenB4.T := (mem_givenB4_T 0).2 (Or.inl rfl)
  have h1 : (1 : ℕ) ∈ givenB4.T := (mem_givenB4_T 1).2 (Or.inr rfl)
  have hall : ∀ x ∈ givenB4.T, merge 0 1 x = 0 := by
    intro x hx
    rcases (mem_givenB4_T x).1 hx with rfl | rfl
    · exact merge_left 0 1
    · exact merge_right 0 1
  have hle : (givenB4.identify 0 1).M (0, 0) ≤ 2 := by
    have htot := total_identify givenB4 (v := 1) h0 (by omega)
    have hgiven : givenB4.total = 2 := by decide
    have hmem : ((0, 0) : ℕ × ℕ) ∈ (givenB4.identify 0 1).T ×ˢ (givenB4.identify 0 1).T := by
      rw [identify_T]
      exact Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨by omega, h0⟩, Finset.mem_erase.2 ⟨by omega, h0⟩⟩
    have hsingle : (givenB4.identify 0 1).M (0, 0) ≤ (givenB4.identify 0 1).total := by
      unfold MSt.total
      exact Finset.single_le_sum (f := (givenB4.identify 0 1).M) (fun _ _ => Nat.zero_le _) hmem
    omega
  have hge := identify_M_ge_pair givenB4 h0 h1 (by omega)
  rw [givenB4_arb, givenB4_bra] at hge
  apply MSt.ext
  · show ({0, 1} : Finset ℕ).erase 1 = {0}
    decide
  · funext p
    by_cases hp : p = (0, 0)
    · subst hp
      rw [loopState_M_self]
      omega
    · rw [identify_M_eq_zero_of_all_merged givenB4 0 1 hall hp, loopState_M_of_ne 2 hp]
  · rfl
  · rfl

theorem step_identify_givenB4 : Step6 givenB4 (loopState 2) :=
  identify_givenB4_eq ▸ Step6.identify _ 0 1 ((mem_givenB4_T 0).2 (Or.inl rfl))
    ((mem_givenB4_T 1).2 (Or.inr rfl)) (by omega)

/-- Removing `bra` from what is given with `bra` gives what is given without it, whose
identification is the one-term state asserting `0r0` once: two changes. -/
theorem givenB4_to_loopState_one : Reach6 givenB4 (loopState 1) 2 := by
  have st1 : Step6 givenB4 givenA4 := givenB4_remove_bra_eq ▸ step_remove_bra_B.toStep6
  exact (Reach6.single st1).step step_identify_givenA4

/-- **Names one term, `bra` given.**  Keep as many of the two givens as the target asserts
`0r0` (up to two): remove the others, identify, add. -/
theorem fewest_changes6_upper_B_merged {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 0) :
    ∃ n, Reach6 givenB4 g n ∧ n + 4 = costB6 g := by
  have heq : g.a = g.b := ha.trans hb.symm
  unfold costB6
  rw [lostB6_of_eq heq, ha]
  by_cases hk0 : g.M (0, 0) = 0
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains oneTerm4_wf hgw (oneTerm4_contains hgw ha hb)
    refine ⟨3 + n, givenB4_to_oneTerm4.toReach6.trans hn, ?_⟩
    rw [size_oneTerm4] at hc
    rw [hk0]
    omega
  · by_cases hk1 : g.M (0, 0) = 1
    · obtain ⟨n, hn, hc⟩ := reach6_of_contains (loopState_wf 1) hgw
        (loopState_contains hgw ha hb (by omega))
      refine ⟨2 + n, givenB4_to_loopState_one.trans hn, ?_⟩
      rw [size_loopState] at hc
      rw [hk1]
      omega
    · obtain ⟨n, hn, hc⟩ := reach6_of_contains (loopState_wf 2) hgw
        (loopState_contains hgw ha hb (by omega))
      refine ⟨1 + n, (Reach6.single step_identify_givenB4).trans hn, ?_⟩
      rw [size_loopState] at hc
      have : min (g.M (0, 0)) 2 = 2 := by omega
      rw [this]
      omega

/-- **Fewest changes, `bra` asserted to begin with.** -/
theorem fewest_changes6_B {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach6 givenB4 g n ∧ n + 4 = costB6 g) ∧ ∀ n, Reach6 givenB4 g n → costB6 g ≤ n + 4 :=
  ⟨hb.elim (fewest_changes6_upper_B_apart hgw ha) (fewest_changes6_upper_B_merged hgw ha),
    fun _ h => fewest_changes6_lower_B h⟩

/-! ## What survives of the fifth derivation's cost -/

/-- On states asserting no `xrx` the fifth's fewest changes survive: the same count, with
the fifth's potential. -/
theorem fewest_changes6_of_legal_A {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach6 givenA4 g n ∧ n + 3 = costA5 g) ∧ ∀ n, Reach6 givenA4 g n → costA5 g ≤ n + 3 := by
  rw [← costA6_eq_costA5_of_legal hg]
  exact fewest_changes6_A hgw ha hb

theorem fewest_changes6_of_legal_B {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach6 givenB4 g n ∧ n + 4 = costB5 g) ∧ ∀ n, Reach6 givenB4 g n → costB5 g ≤ n + 4 := by
  rw [← costB6_eq_costB5_of_legal hg]
  exact fewest_changes6_B hgw ha hb

/-- With the names apart the fifth's cost survives as it stands. -/
theorem fewest_changes6_apart_A {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1) :
    (∃ n, Reach6 givenA4 g n ∧ n + 3 = costA5 g) ∧ ∀ n, Reach6 givenA4 g n → costA5 g ≤ n + 3 := by
  have hne : g.a ≠ g.b := by rw [ha, hb]; omega
  have e : costA6 g = costA5 g := by
    unfold costA6 costA5
    rw [lostA6_eq_lostA5_of_ne hne]
  rw [← e]
  exact fewest_changes6_A hgw ha (Or.inl hb)

theorem lostA6_eq_zero_of_contains {g : MSt} (h : Contains4 givenA4 g) : lostA6 g = 0 := by
  have hm := h.mult (0, 1)
  rw [givenA4_arb] at hm
  rw [lostA6_of_ne (by rw [h.name_a, h.name_b, givenA4_a, givenA4_b]; omega), h.name_a, h.name_b,
    givenA4_a, givenA4_b]
  exact miss5_of_ne_zero (by omega)

theorem lostB6_eq_zero_of_contains {g : MSt} (h : Contains4 givenB4 g) : lostB6 g = 0 := by
  have h1 := h.mult (0, 1)
  have h2 := h.mult (1, 0)
  rw [givenB4_arb] at h1
  rw [givenB4_bra] at h2
  rw [lostB6_of_ne (by rw [h.name_a, h.name_b, givenB4_a, givenB4_b]; omega), h.name_a, h.name_b,
    givenB4_a, givenB4_b, miss5_of_ne_zero (by omega), miss5_of_ne_zero (by omega)]

/-- On a state containing what is given, the fewest changes is the size difference (the
fourth's cost, as under the fifth seed). -/
theorem fewest_changes6_of_contains_A {g : MSt} (hgw : g.WF) (h : Contains4 givenA4 g) :
    (∃ n, Reach6 givenA4 g n ∧ n + 3 = g.size) ∧ ∀ n, Reach6 givenA4 g n → g.size ≤ n + 3 := by
  constructor
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains givenA4_wf hgw h
    rw [size_givenA4] at hc
    exact ⟨n, hn, hc⟩
  · intro n hn
    have := fewest_changes6_lower_A hn
    unfold costA6 at this
    rw [lostA6_eq_zero_of_contains h] at this
    omega

theorem fewest_changes6_of_contains_B {g : MSt} (hgw : g.WF) (h : Contains4 givenB4 g) :
    (∃ n, Reach6 givenB4 g n ∧ n + 4 = g.size) ∧ ∀ n, Reach6 givenB4 g n → g.size ≤ n + 4 := by
  constructor
  · obtain ⟨n, hn, hc⟩ := reach6_of_contains givenB4_wf hgw h
    rw [size_givenB4] at hc
    exact ⟨n, hn, hc⟩
  · intro n hn
    have := fewest_changes6_lower_B hn
    unfold costB6 at this
    rw [lostB6_eq_zero_of_contains h] at this
    omega

/-- **The fifth's potential is no lower bound.**  Identifying `a` and `b` in what is given is
one change, to a state whose fifth-seed cost is `6` — three more than what is given —
while its sixth-seed cost is `4`, one more. -/
theorem fifth_potential_fails :
    Reach6 givenA4 (givenA4.identify 0 1) 1 ∧ costA5 (givenA4.identify 0 1) = 6 ∧
      costA6 (givenA4.identify 0 1) = 4 := by
  rw [identify_givenA4_eq]
  refine ⟨Reach6.single step_identify_givenA4, ?_, ?_⟩
  · unfold costA5
    rw [size_loopState, lostA5_of_eq rfl]
  · unfold costA6
    rw [size_loopState, lostA6_of_eq rfl, loopState_a, loopState_M_self]
    decide

/-- The one-term states asserting `0r0` `k` times cost `k` changes for `k ≥ 1`: the round
of `a (a and b one term); ara(k)` is `k`, not the fifth's `k + 2`. -/
theorem cost_loopState (k : ℕ) (hk : 1 ≤ k) : costA6 (loopState k) = k + 3 := by
  unfold costA6
  rw [size_loopState, lostA6_of_eq rfl, loopState_a, loopState_M_self]
  have : min k 1 = 1 := by omega
  rw [this]

end Seed.Sixth
