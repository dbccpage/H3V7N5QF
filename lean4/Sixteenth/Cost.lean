import Sixteenth.Step

/-!
# Fewest changes with a record that feeds back

The potential of a state is its size (the ninth's) plus twice its record.
Derived here:
* every change moves the potential by exactly one: up on a term, a direct
  assertion and a removal, down on an admission and an identification
  (`Step16.potential_step`, and the five lemmas of `Sixteenth/State.lean`);
  so a state reached from the empty state in `n` changes has potential at most
  `n` (`Reach16.potential_le`, `fewest_changes16_lower`);
* the empty state reaches every well-formed state in exactly its potential
  (`reach16_by_additions`): the ninth's additions to the ninth state through
  the embedding, then an addition and a removal for every recorded leftover
  (`reach16_record`);
* so the fewest changes to a result is its potential (`fewest_changes16`);
* sequences counted with their *falls* (admissions and identifications,
  `ReachD`) satisfy `potential + 2·falls = potential of the start + length`
  (`ReachD.potential`), so **no shortest sequence from the empty beginning
  admits or identifies** (`no_fall_on_shortest16`): an assertion that arrives
  by admission costs three changes where a direct addition costs one
  (`admission_costs_three`).
-/

namespace Seed.Sixteenth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth Seed.Ninth NDSt RSt

/-! ## Every change moves the potential by one -/

theorem Step16.potential_step {s t : RSt} (h : Step16 s t) (hw : s.WF) :
    t.potential = s.potential + 1 ∨ t.potential + 1 = s.potential := by
  cases h with
  | addTerm t ht => exact Or.inl (potential_addTerm hw ht)
  | addAssertion q x y hx hy => exact Or.inl (potential_addAssertion s q hx hy)
  | remove q x y hp => exact Or.inl (potential_remove hw q hp)
  | admitLeftover q x y hl => exact Or.inr (potential_admit hw q hl)
  | identify u v hu hv huv => exact Or.inr (potential_identify hu hv huv)

theorem Step16.potential_le {s t : RSt} (h : Step16 s t) (hw : s.WF) : t.potential ≤ s.potential + 1 := by
  rcases h.potential_step hw with e | e <;> omega

theorem Reach16.potential_le {s t : RSt} {n : ℕ} (h : Reach16 s t n) (hw : s.WF) :
    t.potential ≤ s.potential + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.potential_le (r.wf hw)
    omega

theorem Reach16.potential_parity {s t : RSt} {n : ℕ} (h : Reach16 s t n) (hw : s.WF) :
    (s.potential + t.potential + n) % 2 = 0 := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.potential_step (r.wf hw) with e | e <;> omega

/-- **Lower bound.**  A result reached in `n` changes has potential at most `n`. -/
theorem fewest_changes16_lower {g : RSt} {n : ℕ} (h : Reach16 empty16 g n) : g.potential ≤ n := by
  have := h.potential_le empty16_wf
  rw [empty16_potential] at this
  omega

/-! ## Rises and falls -/

/-- A change that raises the potential: a term, a direct assertion, a removal. -/
inductive Rise16 : RSt → RSt → Prop
  | addTerm (s : RSt) (t : ℕ) (ht : t ∉ s.st.T) : Rise16 s (s.addTerm t)
  | addAssertion (s : RSt) (q : Rel) (x y : ℕ) (hx : x ∈ s.st.T) (hy : y ∈ s.st.T) :
      Rise16 s (s.addAssertion q x y)
  | remove (s : RSt) (q : Rel) (x y : ℕ) (hp : s.st.M q (x, y) ≠ 0) : Rise16 s (s.remove q x y)

/-- A change that lowers the potential: an admission, an identification. -/
inductive Fall16 : RSt → RSt → Prop
  | admitLeftover (s : RSt) (q : Rel) (x y : ℕ) (hl : s.L (x, y) ≠ 0) : Fall16 s (s.admitLeftover q x y)
  | identify (s : RSt) (u v : ℕ) (hu : u ∈ s.st.T) (hv : v ∈ s.st.T) (huv : u ≠ v) :
      Fall16 s (s.identify u v)

theorem Rise16.toStep16 {s t : RSt} (h : Rise16 s t) : Step16 s t := by
  cases h with
  | addTerm t ht => exact Step16.addTerm s t ht
  | addAssertion q x y hx hy => exact Step16.addAssertion s q x y hx hy
  | remove q x y hp => exact Step16.remove s q x y hp

theorem Fall16.toStep16 {s t : RSt} (h : Fall16 s t) : Step16 s t := by
  cases h with
  | admitLeftover q x y hl => exact Step16.admitLeftover s q x y hl
  | identify u v hu hv huv => exact Step16.identify s u v hu hv huv

/-- Every change rises or falls. -/
theorem Step16.rise_or_fall {s t : RSt} (h : Step16 s t) : Rise16 s t ∨ Fall16 s t := by
  cases h with
  | addTerm t ht => exact Or.inl (Rise16.addTerm s t ht)
  | addAssertion q x y hx hy => exact Or.inl (Rise16.addAssertion s q x y hx hy)
  | remove q x y hp => exact Or.inl (Rise16.remove s q x y hp)
  | admitLeftover q x y hl => exact Or.inr (Fall16.admitLeftover s q x y hl)
  | identify u v hu hv huv => exact Or.inr (Fall16.identify s u v hu hv huv)

theorem Rise16.potential {s t : RSt} (h : Rise16 s t) (hw : s.WF) : t.potential = s.potential + 1 := by
  cases h with
  | addTerm t ht => exact potential_addTerm hw ht
  | addAssertion q x y hx hy => exact potential_addAssertion s q hx hy
  | remove q x y hp => exact potential_remove hw q hp

theorem Fall16.potential {s t : RSt} (h : Fall16 s t) (hw : s.WF) : t.potential + 1 = s.potential := by
  cases h with
  | admitLeftover q x y hl => exact potential_admit hw q hl
  | identify u v hu hv huv => exact potential_identify hu hv huv

/-- `ReachD s t n d`: `t` is reached from `s` by `n` changes, `d` of them falls (admissions or
identifications). -/
inductive ReachD : RSt → RSt → ℕ → ℕ → Prop
  | refl (s : RSt) : ReachD s s 0 0
  | rise {s t u : RSt} {n d : ℕ} : ReachD s t n d → Rise16 t u → ReachD s u (n + 1) d
  | fall {s t u : RSt} {n d : ℕ} : ReachD s t n d → Fall16 t u → ReachD s u (n + 1) (d + 1)

theorem ReachD.toReach16 {s t : RSt} {n d : ℕ} (h : ReachD s t n d) : Reach16 s t n := by
  induction h with
  | refl => exact Reach16.refl _
  | rise _ st ih => exact Reach16.step ih st.toStep16
  | fall _ st ih => exact Reach16.step ih st.toStep16

theorem Reach16.toReachD {s t : RSt} {n : ℕ} (h : Reach16 s t n) : ∃ d, ReachD s t n d := by
  induction h with
  | refl => exact ⟨0, ReachD.refl _⟩
  | step _ st ih =>
    obtain ⟨d, r⟩ := ih
    rcases st.rise_or_fall with up | down
    · exact ⟨d, ReachD.rise r up⟩
    · exact ⟨d + 1, ReachD.fall r down⟩

/-- The potential at the end, plus twice the falls, is the potential at the start plus the length. -/
theorem ReachD.potential {s t : RSt} {n d : ℕ} (h : ReachD s t n d) (hw : s.WF) :
    t.potential + 2 * d = s.potential + n := by
  induction h with
  | refl => omega
  | rise r st ih =>
    have := st.potential (r.toReach16.wf hw)
    omega
  | fall r st ih =>
    have := st.potential (r.toReach16.wf hw)
    omega

/-- **No shortest sequence from the empty beginning admits or identifies.** -/
theorem no_fall_on_shortest16 {g : RSt} {n d : ℕ} (h : ReachD empty16 g n d) (hn : n = g.potential) : d = 0 := by
  have := h.potential empty16_wf
  rw [empty16_potential] at this
  omega

/-! ## Additions and removals reach everything -/

/-- A well-formed state with an empty record is the embedding of its ninth state. -/
theorem eq_ofRSt_of_total_zero {s : RSt} (hw : s.WF) (h0 : s.record.total = 0) : s = s.st.ofRSt := by
  apply RSt.ext
  · rfl
  · funext p
    show s.L p = 0
    by_contra hz
    have hmem : p ∈ s.st.T ×ˢ s.st.T := Finset.mem_product.2 (hw.2 p hz)
    have hle : s.L p ≤ ∑ q ∈ s.st.T ×ˢ s.st.T, s.L q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    have : s.record.total = ∑ q ∈ s.st.T ×ˢ s.st.T, s.L q := rfl
    omega

/-- The state with one recorded leftover of `p` fewer. -/
def lowered (s : RSt) (p : ℕ × ℕ) : RSt := ⟨s.st, Function.update s.L p (s.L p - 1)⟩

theorem lowered_rec (s : RSt) (x y : ℕ) : (lowered s (x, y)).record = s.record.remove x y := rfl

theorem lowered_wf {s : RSt} (hw : s.WF) {x y : ℕ} (hl : s.L (x, y) ≠ 0) : (lowered s (x, y)).WF := by
  refine ⟨hw.1, ?_⟩
  show (s.record.remove x y).WF
  exact (Step7.remove s.record x y hl).wf hw.2

theorem lowered_total {s : RSt} (hw : s.WF) {x y : ℕ} (hl : s.L (x, y) ≠ 0) :
    (lowered s (x, y)).record.total + 1 = s.record.total := by
  obtain ⟨hx, hy⟩ := mem_of_L hw hl
  rw [lowered_rec]
  exact Seed.Fifth.total_remove (s.record.name x) hx hy hl

/-- Adding an assertion of the pair and removing it again records one more leftover of it. -/
theorem add_remove_lowered {s : RSt} {x y : ℕ} (hl : s.L (x, y) ≠ 0) :
    ((lowered s (x, y)).addAssertion false x y).remove false x y = s := by
  apply RSt.ext
  · exact Seed.Fourteenth.add_remove s.st false x y
  · funext p
    by_cases hp : p = (x, y)
    · subst hp
      simp [lowered, RSt.addAssertion, RSt.remove]
      omega
    · simp [lowered, RSt.addAssertion, RSt.remove, hp]

/-- From the embedding of its ninth state, a well-formed state is reached in twice its record: an
addition and a removal per recorded leftover. -/
theorem reach16_record (k : ℕ) : ∀ s : RSt, s.WF → s.record.total = k → Reach16 s.st.ofRSt s (2 * k) := by
  induction k with
  | zero =>
    intro s hw h0
    have e := eq_ofRSt_of_total_zero hw h0
    rw [e]
    exact Reach16.refl _
  | succ k ih =>
    intro s hw hk
    have hne : (∑ q ∈ s.st.T ×ˢ s.st.T, s.L q) ≠ 0 := by
      show s.record.total ≠ 0
      omega
    obtain ⟨⟨x, y⟩, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hw0 := lowered_wf hw hl
    have ht0 : (lowered s (x, y)).record.total = k := by
      have := lowered_total hw hl
      omega
    have ih0 : Reach16 s.st.ofRSt (lowered s (x, y)) (2 * k) := ih (lowered s (x, y)) hw0 ht0
    obtain ⟨hx, hy⟩ := mem_of_L hw hl
    have st1 : Step16 (lowered s (x, y)) ((lowered s (x, y)).addAssertion false x y) :=
      Step16.addAssertion _ false x y hx hy
    have st2 : Step16 ((lowered s (x, y)).addAssertion false x y)
        (((lowered s (x, y)).addAssertion false x y).remove false x y) :=
      Step16.remove _ false x y (by rw [st_addAssertion, M_addAssertion_self]; omega)
    rw [add_remove_lowered hl] at st2
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    exact Reach16.step (Reach16.step ih0 st1) st2

/-- **Upper bound.**  From the empty state, every well-formed state is reached in exactly its
potential: the ninth's additions, then an addition and a removal per recorded leftover. -/
theorem reach16_by_additions {g : RSt} (hg : g.WF) : Reach16 empty16 g g.potential := by
  have r1 : AddReach9 empty9 g.st g.st.size := shortest_are_additions9 (reach9_by_additions hg.1) rfl
  have r1' : Reach16 empty16 g.st.ofRSt g.st.size := r1.embed
  have r2 : Reach16 g.st.ofRSt g (2 * g.record.total) := reach16_record g.record.total g hg rfl
  exact r1'.trans r2

/-- **Fewest changes.**  Every well-formed state is reached from the empty state in exactly its
potential and in no fewer changes. -/
theorem fewest_changes16 {g : RSt} (hg : g.WF) :
    Reach16 empty16 g g.potential ∧ ∀ n, Reach16 empty16 g n → g.potential ≤ n :=
  ⟨reach16_by_additions hg, fun _ h => fewest_changes16_lower h⟩

/-- The ninth's cost survives on the results with an empty record: their potential is their size. -/
theorem fewest_changes16_of_empty_record {g : NDSt} (hg : g.WF) :
    Reach16 empty16 g.ofRSt g.size ∧ ∀ n, Reach16 empty16 g.ofRSt n → g.size ≤ n := by
  have := fewest_changes16 (ofRSt_wf hg)
  rw [potential_ofRSt] at this
  exact this

/-! ## The one-term state with one leftover recorded -/

/-- One term, nothing asserted, one leftover `0ℓ0` recorded. -/
def leftOne : RSt := ⟨oneTerm9, Function.update (fun _ => 0) (0, 0) 1⟩

theorem leftOne_wf : leftOne.WF := by
  refine ⟨oneTerm9_wf, ?_⟩
  intro p hp
  have : p = (0, 0) := by
    by_contra h
    simp [leftOne, Function.update_of_ne h] at hp
  subst this
  simp [leftOne, mem_oneTerm9_T]

theorem leftOne_rec_total : leftOne.record.total = 1 := by
  show (∑ q ∈ oneTerm9.T ×ˢ oneTerm9.T, Function.update (fun _ => 0) (0, 0) 1 q) = 1
  have hT : oneTerm9.T = {0} := by
    ext x
    rw [mem_oneTerm9_T]
    simp
  rw [hT]
  simp

theorem leftOne_potential : leftOne.potential = 3 := by
  unfold RSt.potential
  rw [leftOne_rec_total]
  show (empty9.addTerm 0).size + 2 * 1 = 3
  rw [size_oneTerm9]

/-- **The ninth's cost fails off the empty record**: the one-term state with one leftover recorded
costs three changes, its ninth size being one. -/
theorem ninth_cost_fails_off_empty_record :
    leftOne.st.size = 1 ∧ Reach16 empty16 leftOne 3 ∧ ∀ n, Reach16 empty16 leftOne n → 3 ≤ n := by
  have := fewest_changes16 leftOne_wf
  rw [leftOne_potential] at this
  exact ⟨size_oneTerm9 0, this.1, this.2⟩

/-- The one-term state asserting `ara` once (embedded). -/
def ara16 : RSt := (oneTerm9.addAssertion false 0 0).ofRSt

theorem ara16_wf : ara16.WF :=
  ofRSt_wf ((Step9.addAssertion oneTerm9 false 0 0 ((mem_oneTerm9_T 0).2 rfl) ((mem_oneTerm9_T 0).2 rfl)).wf oneTerm9_wf)

theorem ara16_potential : ara16.potential = 2 := by
  rw [ara16, potential_ofRSt, size_addAssertion9 false ((mem_oneTerm9_T 0).2 rfl) ((mem_oneTerm9_T 0).2 rfl)]
  show (empty9.addTerm 0).size + 1 = 2
  rw [size_oneTerm9]

theorem leftOne_admit : leftOne.admitLeftover false 0 0 = ara16 := by
  apply RSt.ext
  · rfl
  · funext p
    by_cases hp : p = (0, 0)
    · subst hp
      simp [leftOne, ara16, RSt.admitLeftover]
    · simp [leftOne, ara16, RSt.admitLeftover]

/-- **An assertion that arrives by admission costs three changes where a direct addition costs
one**: `ara` is two changes from the empty state (a term, the assertion); through the leftover it
is four (a term, the assertion, its removal, its admission), and every shortest sequence to it
admits nothing. -/
theorem admission_costs_three :
    Reach16 empty16 ara16 2 ∧ (∀ n, Reach16 empty16 ara16 n → 2 ≤ n) ∧
      Reach16 empty16 ara16 4 ∧ ∀ n d, ReachD empty16 ara16 n d → n = 2 → d = 0 := by
  have h := fewest_changes16 ara16_wf
  rw [ara16_potential] at h
  refine ⟨h.1, h.2, ?_, ?_⟩
  · have r3 : Reach16 empty16 leftOne 3 := ninth_cost_fails_off_empty_record.2.1
    have st : Step16 leftOne (leftOne.admitLeftover false 0 0) :=
      Step16.admitLeftover leftOne false 0 0 (by simp [leftOne])
    rw [leftOne_admit] at st
    exact Reach16.step r3 st
  · intro n d hd hn
    exact no_fall_on_shortest16 hd (by rw [hn, ara16_potential])

end Seed.Sixteenth
