import Fifth.Cost

/-!
# Reachability under the fifth seed: the names decide

Derived here:
* every assertion can be removed (`reach5_clear`), every term other than the named
  ones can be identified into `a` (`reach5_collapse`), and a name can be moved onto
  a fresh term by adding it and identifying it with the term that carried the name
  (`move_a_pair`, `move_b_pair`, `move_one`); so from the two named terms alone, with
  nothing asserted, any two named terms are reached (`two_names_to`), and then the
  fourth derivation's additions reach any legal well-formed state containing them;
* **the criterion**: a legal well-formed state `g` is reachable from a well-formed
  state `s` exactly when the names, if one term in `s`, are one term in `g`
  (`reach5_iff`); in particular every legal well-formed state is a result of either
  beginning (`result5_iff_A`, `result5_iff_B`) — the first derivation's "everything
  legal is a result" (1:D9), now with the names anywhere and multiplicities counted;
* reachability is mutual on the states with the names apart and on the states with
  them one term (`reach5_symm`), one-way between the two classes
  (`Reach5.names_stay_merged`, `merged_never_apart`); every result with `a ≠ b`
  reaches what is given (`reach5_back_A`, `reach5_back_B`);
* every well-formed state with a term reaches itself in two changes — add a term,
  identify it back (`add_identify_back`, `cycle2`) — so the lengths of the
  sequences reaching a result are unbounded (`Reach5.unbounded`);
* the fourth derivation's one-way reachability does not survive: the two beginnings
  reach each other (`no_return_fails`, `antisymm_fails`).
-/

namespace Seed.Fifth

open Seed Seed.Fourth MSt

/-- The state with the same terms and names and nothing asserted. -/
def cleared (s : MSt) : MSt := ⟨s.T, fun _ => 0, s.a, s.b⟩

theorem cleared_wf {s : MSt} (hw : s.WF) : (cleared s).WF :=
  ⟨fun _ hp => absurd rfl hp, hw.2.1, hw.2.2⟩

/-! ## Removing everything -/

/-- Every unit of multiplicity can be removed, one change each. -/
theorem reach5_clear : ∀ (d : ℕ) (s : MSt), s.WF → s.total = d → Reach5 s (cleared s) d := by
  intro d
  induction d with
  | zero =>
    intro s hw h0
    unfold MSt.total at h0
    have e : s = cleared s := by
      apply MSt.ext
      · rfl
      · funext p
        show s.M p = 0
        by_cases hp : p ∈ s.T ×ˢ s.T
        · exact (Finset.sum_eq_zero_iff.1 h0) p hp
        · by_contra h
          exact hp (Finset.mem_product.2 (hw.1 p h))
      · rfl
      · rfl
    rw [← e]
    exact Reach5.refl s
  | succ d ih =>
    intro s hw hd
    have hne : s.total ≠ 0 := by omega
    unfold MSt.total at hne
    obtain ⟨⟨x, y⟩, hq, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hxy : x ∈ s.T ∧ y ∈ s.T := Finset.mem_product.1 hq
    have st : Step5 s (s.remove x y) := Step5.remove s x y hp
    have ht : (s.remove x y).total = d := by
      have := total_remove s hxy.1 hxy.2 hp
      omega
    have r := ih (s.remove x y) (st.wf hw) ht
    have e : cleared (s.remove x y) = cleared s := rfl
    rw [e] at r
    have := (Reach5.single st).trans r
    rwa [Nat.add_comm] at this

/-! ## Identifying every other term into `a` -/

theorem erase_sdiff_comm' (T K : Finset ℕ) (v : ℕ) : T.erase v \ K = (T \ K).erase v := by
  ext t
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  tauto

/-- With nothing asserted, every term outside `K` (which holds the named terms) can be
identified into `a`, one change each. -/
theorem reach5_collapse : ∀ (d : ℕ) (s : MSt) (K : Finset ℕ), s.WF → (∀ p, s.M p = 0) →
    K ⊆ s.T → s.a ∈ K → s.b ∈ K → (s.T \ K).card = d →
      Reach5 s ⟨K, fun _ => 0, s.a, s.b⟩ d := by
  intro d
  induction d with
  | zero =>
    intro s K hw h0 hK ha hb hd
    have hTK : s.T = K := by
      apply Finset.Subset.antisymm _ hK
      intro t ht
      by_contra htK
      have hmem : t ∈ s.T \ K := Finset.mem_sdiff.2 ⟨ht, htK⟩
      rw [Finset.card_eq_zero] at hd
      rw [hd] at hmem
      exact Finset.notMem_empty t hmem
    have e : s = ⟨K, fun _ => 0, s.a, s.b⟩ := by
      apply MSt.ext
      · exact hTK
      · funext p
        exact h0 p
      · rfl
      · rfl
    rw [← e]
    exact Reach5.refl s
  | succ d ih =>
    intro s K hw h0 hK ha hb hd
    have hne : (s.T \ K).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨v, hv⟩ := hne
    obtain ⟨hvT, hvK⟩ := Finset.mem_sdiff.1 hv
    have hav : s.a ≠ v := fun h => hvK (h ▸ ha)
    have hbv : s.b ≠ v := fun h => hvK (h ▸ hb)
    have st : Step5 s (s.identify s.a v) := Step5.identify s s.a v hw.2.1 hvT hav (h0 _) (h0 _)
    have h0' : ∀ p, (s.identify s.a v).M p = 0 := by
      intro p
      rw [identify_M]
      exact Finset.sum_eq_zero (fun q _ => h0 q)
    have hK' : K ⊆ (s.identify s.a v).T := by
      intro t ht
      rw [identify_T]
      exact Finset.mem_erase.2 ⟨fun h => hvK (h ▸ ht), hK ht⟩
    have ha' : (s.identify s.a v).a ∈ K := by
      rw [identify_a, merge_of_ne hav]
      exact ha
    have hb' : (s.identify s.a v).b ∈ K := by
      rw [identify_b, merge_of_ne hbv]
      exact hb
    have hd' : ((s.identify s.a v).T \ K).card = d := by
      rw [identify_T, erase_sdiff_comm', Finset.card_erase_of_mem hv]
      omega
    have r := ih (s.identify s.a v) K (st.wf hw) h0' hK' ha' hb' hd'
    have e : (⟨K, fun _ => 0, (s.identify s.a v).a, (s.identify s.a v).b⟩ : MSt) =
        ⟨K, fun _ => 0, s.a, s.b⟩ := by
      rw [identify_a, identify_b, merge_of_ne hav, merge_of_ne hbv]
    rw [e] at r
    have := (Reach5.single st).trans r
    rwa [Nat.add_comm] at this

/-! ## Moving the names -/

theorem pair_wf (a b : ℕ) : (⟨{a, b}, fun _ => 0, a, b⟩ : MSt).WF :=
  ⟨fun _ hp => absurd rfl hp, by simp, by simp⟩

/-- The name `a` moves onto a fresh term `c`: add `c`, identify `c` with the term carrying
`a` (the surviving term is the first, `c`). -/
theorem move_a_pair {a b c : ℕ} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Reach5 ⟨{a, b}, fun _ => 0, a, b⟩ ⟨{c, b}, fun _ => 0, c, b⟩ 2 := by
  set s : MSt := ⟨{a, b}, fun _ => 0, a, b⟩ with hs
  have hc : c ∉ s.T := by simp [hs, hca, hcb]
  have st1 : Step5 s (s.addTerm c) := Step5.addTerm s c hc
  have st2 : Step5 (s.addTerm c) ((s.addTerm c).identify c a) :=
    Step5.identify _ c a (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (by simp [hs])) hca
      rfl rfl
  have e : (s.addTerm c).identify c a = ⟨{c, b}, fun _ => 0, c, b⟩ := by
    apply MSt.ext
    · show (insert c ({a, b} : Finset ℕ)).erase a = {c, b}
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    · funext p
      rw [identify_M]
      exact Finset.sum_eq_zero (fun _ _ => rfl)
    · show merge c a a = c
      exact merge_right c a
    · show merge c a b = b
      exact merge_of_ne hab.symm
  rw [← e]
  exact (Reach5.single st1).step st2

/-- The name `b` moves onto a fresh term `d`. -/
theorem move_b_pair {a b d : ℕ} (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    Reach5 ⟨{a, b}, fun _ => 0, a, b⟩ ⟨{a, d}, fun _ => 0, a, d⟩ 2 := by
  set s : MSt := ⟨{a, b}, fun _ => 0, a, b⟩ with hs
  have hd : d ∉ s.T := by simp [hs, hda, hdb]
  have st1 : Step5 s (s.addTerm d) := Step5.addTerm s d hd
  have st2 : Step5 (s.addTerm d) ((s.addTerm d).identify d b) :=
    Step5.identify _ d b (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (by simp [hs])) hdb
      rfl rfl
  have e : (s.addTerm d).identify d b = ⟨{a, d}, fun _ => 0, a, d⟩ := by
    apply MSt.ext
    · show (insert d ({a, b} : Finset ℕ)).erase b = {a, d}
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    · funext p
      rw [identify_M]
      exact Finset.sum_eq_zero (fun _ _ => rfl)
    · show merge d b a = a
      exact merge_of_ne hab
    · show merge d b b = d
      exact merge_right d b
  rw [← e]
  exact (Reach5.single st1).step st2

/-- From the two named terms alone, nothing asserted, to any two named terms: move each
name onto a fresh term, then onto the target's term. -/
theorem two_names_to {a b ga gb : ℕ} (hab : a ≠ b) (hg : ga ≠ gb) :
    Reach5 ⟨{a, b}, fun _ => 0, a, b⟩ ⟨{ga, gb}, fun _ => 0, ga, gb⟩ 8 := by
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({a, b, ga, gb} : Finset ℕ)
  obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset ({a, b, ga, gb, c} : Finset ℕ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
  have r1 := move_a_pair (c := c) hab hc.1 hc.2.1
  have r2 := move_b_pair (a := c) (b := b) (d := d) hc.2.1 hd.2.2.2.2 hd.2.1
  have r3 := move_a_pair (a := c) (b := d) (c := ga) (Ne.symm hd.2.2.2.2) (Ne.symm hc.2.2.1) (Ne.symm hd.2.2.1)
  have r4 := move_b_pair (a := ga) (b := d) (d := gb) (Ne.symm hd.2.2.1) (Ne.symm hg) (Ne.symm hd.2.2.2.1)
  exact ((r1.trans r2).trans r3).trans r4

/-- Identifying `a` and `b` when nothing is asserted: the names become one term. -/
theorem merge_names {a b : ℕ} (hab : a ≠ b) :
    Reach5 ⟨{a, b}, fun _ => 0, a, b⟩ ⟨{a, a}, fun _ => 0, a, a⟩ 1 := by
  set s : MSt := ⟨{a, b}, fun _ => 0, a, b⟩ with hs
  have st : Step5 s (s.identify a b) :=
    Step5.identify s a b (by simp [hs]) (by simp [hs]) hab rfl rfl
  have e : s.identify a b = ⟨{a, a}, fun _ => 0, a, a⟩ := by
    apply MSt.ext
    · show ({a, b} : Finset ℕ).erase b = {a, a}
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    · funext p
      rw [identify_M]
      exact Finset.sum_eq_zero (fun _ _ => rfl)
    · show merge a b a = a
      exact merge_left a b
    · show merge a b b = a
      exact merge_right a b
  rw [← e]
  exact Reach5.single st

/-- The one term carrying both names moves onto any term. -/
theorem move_one (a ga : ℕ) :
    ∃ n, Reach5 ⟨{a, a}, fun _ => 0, a, a⟩ ⟨{ga, ga}, fun _ => 0, ga, ga⟩ n := by
  by_cases h : ga = a
  · subst h
    exact ⟨0, Reach5.refl _⟩
  · set s : MSt := ⟨{a, a}, fun _ => 0, a, a⟩ with hs
    have hga : ga ∉ s.T := by simp [hs, h]
    have st1 : Step5 s (s.addTerm ga) := Step5.addTerm s ga hga
    have st2 : Step5 (s.addTerm ga) ((s.addTerm ga).identify ga a) :=
      Step5.identify _ ga a (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (by simp [hs])) h
        rfl rfl
    have e : (s.addTerm ga).identify ga a = ⟨{ga, ga}, fun _ => 0, ga, ga⟩ := by
      apply MSt.ext
      · show (insert ga ({a, a} : Finset ℕ)).erase a = {ga, ga}
        ext t
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        omega
      · funext p
        rw [identify_M]
        exact Finset.sum_eq_zero (fun _ _ => rfl)
      · show merge ga a a = ga
        exact merge_right ga a
      · show merge ga a a = ga
        exact merge_right ga a
    refine ⟨2, ?_⟩
    rw [← e]
    exact (Reach5.single st1).step st2

/-! ## The criterion -/

/-- **Sufficiency.**  From a well-formed state whose names, if one term, are one term in
the target: remove everything, identify every other term into `a`, move the names,
then add what the target has. -/
theorem reach5_of_names {s g : MSt} (hs : s.WF) (hg : g.Legal) (hgw : g.WF)
    (h : s.a = s.b → g.a = g.b) : ∃ n, Reach5 s g n := by
  have r1 := reach5_clear s.total s hs rfl
  have hK : ({s.a, s.b} : Finset ℕ) ⊆ (cleared s).T := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hs.2.1
    · exact hs.2.2
  have r2 := reach5_collapse _ (cleared s) {s.a, s.b} (cleared_wf hs) (fun _ => rfl) hK
    (by simp [cleared]) (by simp [cleared]) rfl
  have r3 : ∃ m, Reach5 ⟨{s.a, s.b}, fun _ => 0, s.a, s.b⟩ ⟨{g.a, g.b}, fun _ => 0, g.a, g.b⟩ m := by
    by_cases hab : s.a = s.b
    · have hgab := h hab
      rw [hab, hgab]
      exact move_one s.b g.b
    · by_cases hgab : g.a = g.b
      · rw [hgab]
        obtain ⟨m, hm⟩ := move_one s.a g.b
        exact ⟨1 + m, (merge_names hab).trans hm⟩
      · exact ⟨8, two_names_to hab hgab⟩
  obtain ⟨m, r3⟩ := r3
  have hc : Contains4 ⟨{g.a, g.b}, fun _ => 0, g.a, g.b⟩ g := by
    refine ⟨fun t ht => ?_, fun _ => Nat.zero_le _, rfl, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hgw.2.1
    · exact hgw.2.2
  obtain ⟨k, r4, _⟩ := reach4_of_contains (pair_wf g.a g.b) hg hgw hc
  exact ⟨_, ((r1.trans r2).trans r3).trans r4.toReach5⟩

/-- **Reachability is decided by the names.**  A legal, well-formed state is reachable
from a well-formed state exactly when the names, if one term at the start, are one
term at the end. -/
theorem reach5_iff {s g : MSt} (hs : s.WF) (hg : g.Legal) (hgw : g.WF) :
    (∃ n, Reach5 s g n) ↔ (s.a = s.b → g.a = g.b) :=
  ⟨fun ⟨_, h⟩ hab => h.names_stay_merged hab, reach5_of_names hs hg hgw⟩

/-- **The results, `bra` not asserted to begin with:** every legal well-formed state,
with its names anywhere. -/
theorem result5_iff_A (g : MSt) : (∃ n, Reach5 givenA4 g n) ↔ (g.Legal ∧ g.WF) :=
  ⟨fun ⟨_, h⟩ => ⟨h.legal givenA4_legal, h.wf givenA4_wf⟩,
    fun ⟨hg, hgw⟩ => reach5_of_names givenA4_wf hg hgw
      (fun h => absurd h (by rw [givenA4_a, givenA4_b]; omega))⟩

/-- **The results, `bra` asserted to begin with:** the same. -/
theorem result5_iff_B (g : MSt) : (∃ n, Reach5 givenB4 g n) ↔ (g.Legal ∧ g.WF) :=
  ⟨fun ⟨_, h⟩ => ⟨h.legal givenB4_legal, h.wf givenB4_wf⟩,
    fun ⟨hg, hgw⟩ => reach5_of_names givenB4_wf hg hgw
      (fun h => absurd h (by rw [givenB4_a, givenB4_b]; omega))⟩

/-- Reachability is mutual within the two classes: if `g` is reachable from `s` and
the names of `g`, if one term, are one term in `s`, then `s` is reachable from `g`. -/
theorem reach5_symm {s g : MSt} (hs : s.Legal) (hsw : s.WF) (hgw : g.WF)
    (h : g.a = g.b → s.a = s.b) : ∃ n, Reach5 g s n :=
  reach5_of_names hgw hs hsw h

/-- Every result with `a` and `b` two terms reaches what is given. -/
theorem reach5_back_A {g : MSt} (_hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b) :
    ∃ n, Reach5 g givenA4 n :=
  reach5_of_names hgw givenA4_legal givenA4_wf (fun h => absurd h hne)

theorem reach5_back_B {g : MSt} (_hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b) :
    ∃ n, Reach5 g givenB4 n :=
  reach5_of_names hgw givenB4_legal givenB4_wf (fun h => absurd h hne)

/-- Any two results are comparable: one of them reaches the other (a state with the
names apart reaches everything; two states with the names one term reach each other). -/
theorem reach5_total {s g : MSt} (hs : s.Legal) (hsw : s.WF) (hg : g.Legal) (hgw : g.WF) :
    (∃ n, Reach5 s g n) ∨ ∃ n, Reach5 g s n := by
  by_cases hab : s.a = s.b
  · by_cases hgab : g.a = g.b
    · exact Or.inl (reach5_of_names hsw hg hgw (fun _ => hgab))
    · exact Or.inr (reach5_of_names hgw hs hsw (fun h => absurd h hgab))
  · exact Or.inl (reach5_of_names hsw hg hgw (fun h => absurd h hab))

/-- One-way between the classes: from the one-term state, what is given is never
reached again. -/
theorem merged_never_apart (n : ℕ) : ¬ Reach5 oneTerm4 givenA4 n := by
  intro h
  have := h.names_stay_merged rfl
  rw [givenA4_a, givenA4_b] at this
  omega

/-! ## Every state reaches itself in two changes -/

/-- Adding a term and identifying an old term with it gives the state back. -/
theorem add_identify_back {s : MSt} (hw : s.WF) {x t : ℕ} (hx : x ∈ s.T) (ht : t ∉ s.T) :
    (s.addTerm t).identify x t = s := by
  apply MSt.ext
  · show (insert t s.T).erase t = s.T
    exact Finset.erase_insert ht
  · funext p
    rw [identify_M]
    show ∑ q ∈ ((insert t s.T) ×ˢ (insert t s.T)).filter
      (fun q => (merge x t q.1, merge x t q.2) = p), s.M q = s.M p
    by_cases hp : p.1 ∈ s.T ∧ p.2 ∈ s.T
    · apply Finset.sum_eq_single_of_mem p
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨Finset.mem_insert_of_mem hp.1, Finset.mem_insert_of_mem hp.2⟩, ?_⟩
        rw [merge_of_ne (ne_of_notMem hp.1 ht), merge_of_ne (ne_of_notMem hp.2 ht)]
      · intro q hq hqp
        rw [Finset.mem_filter] at hq
        by_contra hne
        obtain ⟨h1, h2⟩ := hw.1 q hne
        rw [merge_of_ne (ne_of_notMem h1 ht), merge_of_ne (ne_of_notMem h2 ht)] at hq
        exact hqp (by simpa using hq.2)
    · have h0 : s.M p = 0 := by
        by_contra h
        exact hp (hw.1 p h)
      rw [h0]
      apply Finset.sum_eq_zero
      intro q hq
      rw [Finset.mem_filter] at hq
      by_contra hne
      obtain ⟨h1, h2⟩ := hw.1 q hne
      rw [merge_of_ne (ne_of_notMem h1 ht), merge_of_ne (ne_of_notMem h2 ht)] at hq
      apply hp
      rw [← hq.2]
      exact ⟨h1, h2⟩
  · show merge x t s.a = s.a
    exact merge_of_ne (ne_of_notMem hw.2.1 ht)
  · show merge x t s.b = s.b
    exact merge_of_ne (ne_of_notMem hw.2.2 ht)

/-- Every well-formed state with a term reaches itself in two changes. -/
theorem cycle2 {s : MSt} (hw : s.WF) (hne : s.T.Nonempty) : Reach5 s s 2 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset s.T
  have st1 : Step5 s (s.addTerm t) := Step5.addTerm s t ht
  have st2 : Step5 (s.addTerm t) ((s.addTerm t).identify x t) :=
    Step5.identify _ x t (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self t s.T)
      (fun h => ht (h ▸ hx))
      (by
        show s.M (x, t) = 0
        by_contra h
        exact ht (hw.1 _ h).2)
      (by
        show s.M (t, x) = 0
        by_contra h
        exact ht (hw.1 _ h).1)
  rw [add_identify_back hw hx ht] at st2
  exact (Reach5.single st1).step st2

theorem Reach5.cycles {s : MSt} (hw : s.WF) (hne : s.T.Nonempty) (k : ℕ) : Reach5 s s (2 * k) := by
  induction k with
  | zero => exact Reach5.refl s
  | succ k ih =>
    have := ih.trans (cycle2 hw hne)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact this

/-- The lengths of the sequences reaching a result are unbounded. -/
theorem Reach5.unbounded {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hw : s.WF) (hne : s.T.Nonempty)
    (k : ℕ) : Reach5 s t (2 * k + n) :=
  (Reach5.cycles hw hne k).trans h

/-! ## What does not survive: one-way reachability -/

theorem givenB4_remove_bra_eq : givenB4.remove 1 0 = givenA4 := by
  apply MSt.ext
  · rfl
  · funext p
    rw [remove_M, Function.update_apply]
    by_cases hp : p = (1, 0)
    · subst hp
      rw [if_pos rfl, givenB4_bra, givenA4_bra]
    · rw [if_neg hp, givenB4_M, givenA4_M]
      simp only [givenA, givenB, Finset.mem_insert, Finset.mem_singleton, hp, or_false]
  · rfl
  · rfl

/-- The two beginnings reach each other: a state once left can be returned to. -/
theorem no_return_fails : Reach5 givenA4 givenB4 1 ∧ Reach5 givenB4 givenA4 1 :=
  ⟨givenA4_to_givenB4.toReach5, by
    have := Reach5.single (Step5.remove givenB4 1 0 (by rw [givenB4_bra]; omega))
    rwa [givenB4_remove_bra_eq] at this⟩

/-- Two different results reachable from each other. -/
theorem antisymm_fails : givenA4 ≠ givenB4 ∧ (∃ n, Reach5 givenA4 givenB4 n) ∧ ∃ m, Reach5 givenB4 givenA4 m :=
  ⟨fun h => by
      have := congrArg (fun s : MSt => s.M (1, 0)) h
      simp only [givenA4_bra, givenB4_bra] at this
      exact absurd this (by decide),
    ⟨1, no_return_fails.1⟩, ⟨1, no_return_fails.2⟩⟩

/-- Two sequences of different lengths reach one result. -/
theorem length_not_unique : Reach5 givenA4 givenA4 0 ∧ Reach5 givenA4 givenA4 2 :=
  ⟨Reach5.refl _, no_return_fails.1.trans no_return_fails.2⟩

end Seed.Fifth
