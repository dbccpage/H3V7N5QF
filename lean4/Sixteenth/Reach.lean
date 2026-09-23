import Sixteenth.Cost

/-!
# Reachability with a record that feeds back: the mass is carried, never lost

Derived here:
* **the mass never falls** along a change (`Step16.mass_le`) nor along a
  sequence (`Reach16.mass_le`): a removal moves one unit from a multiplicity
  into the record, an admission moves it back, an identification adds up,
  additions raise;
* so **the ninth's criterion fails**: the one-term state asserting `ara` once
  reaches the one-term state asserting nothing under the ninth seed and never
  here (`has_term_criterion_fails16`), and reachability among the states with
  a term is one-way again (`one_way16`);
* **the results are every well-formed state**, a ninth state with any record
  over its terms (`result16_iff`), the ninth's results being exactly those with
  an empty record (`results_ninth_iff16`); they are jointly free
  (`results_pair16`);
* every state with a term reaches itself in two changes — a term added and
  identified away (`cycle2_16`), and, with an assertion, its removal and the
  admission of the leftover (`cycle2_assert16`) — while the ninth's
  add-then-remove is no longer a cycle (`add_remove_ne`); the lengths of the
  sequences reaching a result are unbounded (`Reach16.unbounded`), so the
  feedback does not terminate;
* a state reaches an empty-record state by admitting every leftover
  (`reach16_admit_all`);
* the exchange of the relations keeps reachability (`reach16_swap`).
-/

namespace Seed.Sixteenth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth Seed.Ninth NDSt RSt

/-! ## The mass never falls -/

theorem Step16.mass_le {s t : RSt} (h : Step16 s t) (hw : s.WF) : s.mass ≤ t.mass := by
  cases h with
  | addTerm t ht => rw [mass_addTerm hw]
  | addAssertion q x y hx hy => rw [mass_addAssertion s q hx hy]; omega
  | remove q x y hp => rw [mass_remove hw q hp]
  | admitLeftover q x y hl => rw [mass_admit hw q hl]
  | identify u v hu hv huv => rw [mass_identify hu huv]

theorem Reach16.mass_le {s t : RSt} {n : ℕ} (h : Reach16 s t n) (hw : s.WF) : s.mass ≤ t.mass := by
  induction h with
  | refl => exact le_refl _
  | step r st ih => exact le_trans ih (st.mass_le (r.wf hw))

/-! ## The ninth's criterion fails -/

/-- The one-term state asserting nothing, embedded. -/
def oneTerm16 : RSt := oneTerm9.ofRSt

theorem oneTerm16_wf : oneTerm16.WF := ofRSt_wf oneTerm9_wf

theorem oneTerm16_mass : oneTerm16.mass = 0 := by
  rw [oneTerm16, mass_ofRSt]
  show (Seed.Seventh.empty.addTerm 0).total + (Seed.Seventh.empty.addTerm 0).total = 0
  rw [total_addTerm7 empty_wf, empty_total]

theorem ara16_mass : ara16.mass = 1 := by
  rw [ara16, mass_ofRSt]
  have h0 : (0 : ℕ) ∈ oneTerm9.T := (mem_oneTerm9_T 0).2 rfl
  rw [total_proj_addAssertion_self oneTerm9 false h0 h0, proj9_addAssertion_other oneTerm9 (by decide) 0 0]
  show (Seed.Seventh.empty.addTerm 0).total + 1 + (Seed.Seventh.empty.addTerm 0).total = 1
  rw [total_addTerm7 empty_wf, empty_total]

/-- **The has-a-term criterion does not survive.**  `ara` once reaches the one-term state asserting
nothing under the ninth seed, and never here: its mass would fall. -/
theorem has_term_criterion_fails16 :
    (∃ n, Reach9 ara16.st oneTerm16.st n) ∧ ∀ n, ¬ Reach16 ara16 oneTerm16 n := by
  constructor
  · exact reach9_of_nonempty ara16_wf.1 oneTerm9_wf ⟨0, (mem_oneTerm9_T 0).2 rfl⟩ ⟨0, (mem_oneTerm9_T 0).2 rfl⟩
  · intro n h
    have := h.mass_le ara16_wf
    rw [ara16_mass, oneTerm16_mass] at this
    omega

/-- Reachability among the states with a term is one-way again: the one-term state reaches `ara`
and not the converse. -/
theorem one_way16 : Reach16 oneTerm16 ara16 1 ∧ ∀ n, ¬ Reach16 ara16 oneTerm16 n :=
  ⟨Reach16.single (Step16.addAssertion oneTerm16 false 0 0 ((mem_oneTerm9_T 0).2 rfl) ((mem_oneTerm9_T 0).2 rfl)),
    has_term_criterion_fails16.2⟩

/-! ## The results -/

/-- **The results are every well-formed state.** -/
theorem result16_iff (g : RSt) : (∃ n, Reach16 empty16 g n) ↔ g.WF :=
  ⟨fun ⟨_, h⟩ => h.wf empty16_wf, fun hw => ⟨_, reach16_by_additions hw⟩⟩

theorem wf_of_ofRSt {g : NDSt} (h : g.ofRSt.WF) : g.WF := h.1

/-- **The ninth's results are exactly the results with an empty record.** -/
theorem results_ninth_iff16 (g : NDSt) : (∃ n, Reach16 empty16 g.ofRSt n) ↔ ∃ n, Reach9 empty9 g n := by
  rw [result16_iff, result9_iff]
  exact ⟨wf_of_ofRSt, ofRSt_wf⟩

/-- A well-formed record on the terms of a ninth state. -/
def RecordOn (g : NDSt) (L : ℕ × ℕ → ℕ) : Prop := ∀ p, L p ≠ 0 → p.1 ∈ g.T ∧ p.2 ∈ g.T

/-- **Jointly free, with any record**: two well-formed parts on the same terms and any record on
those terms make a result. -/
theorem results_pair16 {m m' : NSt} (hm : m.WF) (hm' : m'.WF) (hT : m'.T = m.T) {L : ℕ × ℕ → ℕ}
    (hL : ∀ p, L p ≠ 0 → p.1 ∈ m.T ∧ p.2 ∈ m.T) :
    ∃ n, Reach16 empty16 ⟨⟨m.T, fun q => match q with | false => m.M | true => m'.M⟩, L⟩ n := by
  apply (result16_iff _).2
  refine ⟨⟨hm, ?_⟩, hL⟩
  show (⟨m.T, m'.M⟩ : NSt).WF
  rw [← hT]
  exact hm'

/-! ## Cycles: the feedback does not terminate -/

/-- Every state with an assertion reaches itself in two changes: remove it, admit its leftover. -/
theorem cycle2_assert16 {s : RSt} (q : Rel) {x y : ℕ} (hp : s.st.M q (x, y) ≠ 0) : Reach16 s s 2 := by
  have st1 : Step16 s (s.remove q x y) := Step16.remove s q x y hp
  have st2 : Step16 (s.remove q x y) ((s.remove q x y).admitLeftover q x y) :=
    Step16.admitLeftover _ q x y (by rw [L_remove_self]; omega)
  rw [remove_admit_same s q hp] at st2
  exact Reach16.step (Reach16.single st1) st2

/-- Every well-formed state with a term reaches itself in two changes: a term added and identified
away. -/
theorem cycle2_16 {s : RSt} (hw : s.WF) (hne : s.st.T.Nonempty) : Reach16 s s 2 := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset s.st.T
  have st1 : Step16 s (s.addTerm t) := Step16.addTerm s t ht
  have st2 : Step16 (s.addTerm t) ((s.addTerm t).identify c t) :=
    Step16.identify _ c t (Finset.mem_insert_of_mem hc) (Finset.mem_insert_self t _) (fun h => ht (h ▸ hc))
  rw [identify_addTerm16 hw hc ht] at st2
  exact Reach16.step (Reach16.single st1) st2

theorem Reach16.cycles {s : RSt} (hw : s.WF) (hne : s.st.T.Nonempty) (k : ℕ) : Reach16 s s (2 * k) := by
  induction k with
  | zero => exact Reach16.refl s
  | succ k ih =>
    have := ih.trans (cycle2_16 hw hne)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact this

/-- The lengths of the sequences reaching a result from a state with a term are unbounded: the
feedback does not terminate. -/
theorem Reach16.unbounded {s t : RSt} {n : ℕ} (h : Reach16 s t n) (hw : s.WF) (hne : s.st.T.Nonempty) (k : ℕ) :
    Reach16 s t (2 * k + n) :=
  (Reach16.cycles hw hne k).trans h

/-- A leftover can be admitted and re-removed without bound: `ara` reaches itself in `2k` changes
by removing and admitting, for every `k`. -/
theorem admit_remove_unbounded (k : ℕ) : Reach16 ara16 ara16 (2 * k) := by
  induction k with
  | zero => exact Reach16.refl _
  | succ k ih =>
    have c : Reach16 ara16 ara16 2 := cycle2_assert16 (s := ara16) false (x := 0) (y := 0) (by
      show (oneTerm9.addAssertion false 0 0).M false (0, 0) ≠ 0
      rw [M_addAssertion_self]
      omega)
    have := ih.trans c
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact this

/-! ## Admitting every leftover -/

/-- Admitting one leftover of `p` into `r`: the state with that leftover admitted. -/
theorem admit_lowered {s : RSt} {x y : ℕ} (_hl : s.L (x, y) ≠ 0) :
    s.admitLeftover false x y = ⟨s.st.addAssertion false x y, (lowered s (x, y)).L⟩ := rfl

/-- From a well-formed state, admitting every recorded leftover (into `r`) reaches a state with an
empty record in as many changes as there are leftovers. -/
theorem reach16_admit_all (k : ℕ) :
    ∀ s : RSt, s.WF → s.record.total = k → ∃ g : NDSt, g.WF ∧ g.T = s.st.T ∧ Reach16 s g.ofRSt k := by
  induction k with
  | zero =>
    intro s hw h0
    refine ⟨s.st, hw.1, rfl, ?_⟩
    rw [eq_ofRSt_of_total_zero hw h0]
    exact Reach16.refl _
  | succ k ih =>
    intro s hw hk
    have hne : (∑ q ∈ s.st.T ×ˢ s.st.T, s.L q) ≠ 0 := by
      show s.record.total ≠ 0
      omega
    obtain ⟨⟨x, y⟩, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have st : Step16 s (s.admitLeftover false x y) := Step16.admitLeftover s false x y hl
    have hw' : (s.admitLeftover false x y).WF := st.wf hw
    have ht' : (s.admitLeftover false x y).record.total = k := by
      have := record_total_admit hw false hl
      omega
    obtain ⟨g, hg, hT, r⟩ := ih (s.admitLeftover false x y) hw' ht'
    refine ⟨g, hg, hT, ?_⟩
    rw [show k + 1 = 1 + k by omega]
    exact (Reach16.single st).trans r

/-! ## The exchange keeps reachability -/

theorem reach16_swap {s g : RSt} {n : ℕ} (h : Reach16 s g n) : Reach16 s.swap g.swap n := h.swap

theorem result16_swap {g : RSt} {n : ℕ} (h : Reach16 empty16 g n) : Reach16 empty16 g.swap n := by
  have := h.swap
  have e : empty16.swap = empty16 := by
    apply RSt.ext
    · exact swap9_empty
    · rfl
  rwa [e] at this

end Seed.Sixteenth
