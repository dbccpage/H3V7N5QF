import Fifteenth.Rename

/-!
# States with a record that feeds back

`prompt/sixteenth/seed_prompt.md` is the fourteenth seed with one sentence
changed: a recorded leftover `xℓy` may be admitted, adding the assertion `xry`
or the assertion `xsy`; an unadmitted leftover is not an assertion.  A leftover
recorded off the result could not be reached by a later change on the result,
so the unadmitted leftovers are carried by the state:

* `RSt`: a ninth state (`NDSt`: terms and a multiplicity function for each
  relation) together with its *record* `L`, how many leftovers of each ordered
  pair are recorded and not admitted.  The record is a one-relation counted
  state on the same terms (`RSt.record`, a seventh `NSt`), so the seventh's,
  fifth's and fourth's lemmas about one multiplicity function apply to it
  unchanged: that is the reuse, not a reproof.
* The five operations: a term and a direct assertion act on the ninth state and
  leave the record; a removal lowers a multiplicity and raises the record of
  its pair; an *admission* raises a multiplicity and lowers the record of its
  pair; an identification merges both the ninth state (the ninth's `identify`)
  and the record (the seventh's `identify`, the counts of the merged pairs
  adding up).
* `potential`: the ninth's size plus twice the record (the cost, a theorem of
  `Sixteenth/Cost.lean`); `mass`: both totals plus the record (what no change
  lowers, `Sixteenth/Reach.lean`).
* `RSt.toNDSt` forgets the record; `NDSt.ofRSt` reads a ninth state as a
  sixteenth state with an empty record.  `empty16` is the beginning.

Derived here: the record projects and the operations commute with the
projections definitionally (`record_remove`, `record_admit`, `record_identify`, …);
the potential and the mass of every operation (`potential_addTerm`, …,
`mass_admit`, …) from the ninth's size lemmas and the earlier total lemmas on
the record; a term added and then identified away leaves a one-relation state
as it was (`NSt.identify_addTerm`), hence a ninth state and a sixteenth state
(`identify_addTerm9`, `identify_addTerm16`); the two headline identities of
the paper: removing an assertion and admitting its leftover into the same
relation is the identity on the state (`remove_admit_same`), while admitting
it into the other relation, or adding the assertion directly, is not
(`remove_admit_other_ne`, `remove_admit_other_ne_direct`).
-/

namespace Seed.Sixteenth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth Seed.Ninth NDSt

/-- A state of the sixteenth seed: a ninth state and its record of unadmitted leftovers. -/
@[ext]
structure RSt where
  st : NDSt
  L : ℕ × ℕ → ℕ

namespace RSt

/-- The terms: those of the ninth state. -/
def T (s : RSt) : Finset ℕ := s.st.T

/-- The record as a one-relation counted state on the same terms. -/
def record (s : RSt) : NSt := ⟨s.st.T, s.L⟩

/-- Well formed: the ninth state is, and the record names only terms that are there. -/
def WF (s : RSt) : Prop := s.st.WF ∧ s.record.WF

/-- Adding a term: to the ninth state; the record is unchanged. -/
def addTerm (s : RSt) (t : ℕ) : RSt := ⟨s.st.addTerm t, s.L⟩

/-- Adding an assertion directly: the record is unchanged. -/
def addAssertion (s : RSt) (q : Rel) (x y : ℕ) : RSt := ⟨s.st.addAssertion q x y, s.L⟩

/-- Removing an assertion: its multiplicity falls by one and a leftover of its pair is recorded. -/
def remove (s : RSt) (q : Rel) (x y : ℕ) : RSt :=
  ⟨s.st.remove q x y, Function.update s.L (x, y) (s.L (x, y) + 1)⟩

/-- Admitting a recorded leftover into relation `q`: the multiplicity of `xqy` rises by one and the
record of the pair falls by one. -/
def admitLeftover (s : RSt) (q : Rel) (x y : ℕ) : RSt :=
  ⟨s.st.addAssertion q x y, Function.update s.L (x, y) (s.L (x, y) - 1)⟩

/-- Identifying `u` and `v` in every assertion and in the record: the counts of the pairs that become
one pair add up, in each relation and in the record. -/
def identify (s : RSt) (u v : ℕ) : RSt :=
  ⟨s.st.identify u v,
    fun p => ∑ w ∈ (s.st.T ×ˢ s.st.T).filter (fun w => (merge u v w.1, merge u v w.2) = p), s.L w⟩

/-- The ninth's size plus twice the record. -/
def potential (s : RSt) : ℕ := s.st.size + 2 * s.record.total

/-- Both totals plus the record. -/
def mass (s : RSt) : ℕ := (s.st.proj false).total + (s.st.proj true).total + s.record.total

/-- The record forgotten. -/
def toNDSt (s : RSt) : NDSt := s.st

/-- The two relations exchanged; the record, naming no relation, is unchanged. -/
def swap (s : RSt) : RSt := ⟨s.st.swap, s.L⟩

end RSt

open RSt

/-- A ninth state read as a sixteenth state with an empty record. -/
def _root_.Seed.Ninth.NDSt.ofRSt (g : NDSt) : RSt := ⟨g, fun _ => 0⟩

/-- What is given: no terms, nothing asserted, nothing recorded. -/
def empty16 : RSt := empty9.ofRSt

/-! ## Projections of the operations -/

@[simp] theorem record_T (s : RSt) : s.record.T = s.st.T := rfl
@[simp] theorem record_M (s : RSt) : s.record.M = s.L := rfl
@[simp] theorem T_eq (s : RSt) : s.T = s.st.T := rfl

theorem st_addTerm (s : RSt) (t : ℕ) : (s.addTerm t).st = s.st.addTerm t := rfl
theorem st_addAssertion (s : RSt) (q : Rel) (x y : ℕ) : (s.addAssertion q x y).st = s.st.addAssertion q x y := rfl
theorem st_remove (s : RSt) (q : Rel) (x y : ℕ) : (s.remove q x y).st = s.st.remove q x y := rfl
theorem st_admit (s : RSt) (q : Rel) (x y : ℕ) : (s.admitLeftover q x y).st = s.st.addAssertion q x y := rfl
theorem st_identify (s : RSt) (u v : ℕ) : (s.identify u v).st = s.st.identify u v := rfl

theorem record_addTerm (s : RSt) (t : ℕ) : (s.addTerm t).record = s.record.addTerm t := rfl
theorem record_addAssertion (s : RSt) (q : Rel) (x y : ℕ) : (s.addAssertion q x y).record = s.record := rfl
theorem record_remove (s : RSt) (q : Rel) (x y : ℕ) : (s.remove q x y).record = s.record.addAssertion x y := rfl
theorem record_admit (s : RSt) (q : Rel) (x y : ℕ) : (s.admitLeftover q x y).record = s.record.remove x y := rfl
theorem record_identify (s : RSt) (u v : ℕ) : (s.identify u v).record = s.record.identify u v := rfl

theorem L_addTerm (s : RSt) (t : ℕ) : (s.addTerm t).L = s.L := rfl
theorem L_addAssertion (s : RSt) (q : Rel) (x y : ℕ) : (s.addAssertion q x y).L = s.L := rfl

@[simp] theorem ofRSt_st (g : NDSt) : g.ofRSt.st = g := rfl
@[simp] theorem ofRSt_L (g : NDSt) (p : ℕ × ℕ) : g.ofRSt.L p = 0 := rfl
theorem toNDSt_ofRSt (g : NDSt) : g.ofRSt.toNDSt = g := rfl
@[simp] theorem empty16_st : empty16.st = empty9 := rfl
@[simp] theorem empty16_L (p : ℕ × ℕ) : empty16.L p = 0 := rfl

theorem ofRSt_rec (g : NDSt) : g.ofRSt.record = ⟨g.T, fun _ => 0⟩ := rfl

theorem ofRSt_rec_total (g : NDSt) : g.ofRSt.record.total = 0 := total_zero9 g.T

theorem ofRSt_wf {g : NDSt} (hg : g.WF) : g.ofRSt.WF := ⟨hg, fun _ h => absurd rfl h⟩

theorem empty16_wf : empty16.WF := ofRSt_wf empty9_wf

theorem potential_ofRSt (g : NDSt) : g.ofRSt.potential = g.size := by
  unfold RSt.potential
  rw [ofRSt_rec_total]
  rfl

theorem empty16_potential : empty16.potential = 0 := by
  rw [show empty16 = empty9.ofRSt from rfl, potential_ofRSt, empty9_size]

theorem mass_ofRSt (g : NDSt) : g.ofRSt.mass = (g.proj false).total + (g.proj true).total := by
  unfold RSt.mass
  rw [ofRSt_rec_total]
  rfl

theorem wf_st {s : RSt} (hw : s.WF) : s.st.WF := hw.1
theorem wf_rec {s : RSt} (hw : s.WF) : s.record.WF := hw.2

/-- A recorded pair names two terms that are there. -/
theorem mem_of_L {s : RSt} (hw : s.WF) {x y : ℕ} (h : s.L (x, y) ≠ 0) : x ∈ s.st.T ∧ y ∈ s.st.T :=
  hw.2 (x, y) h

/-- An asserted pair names two terms that are there. -/
theorem mem_of_M {s : RSt} (hw : s.WF) (q : Rel) {x y : ℕ} (h : s.st.M q (x, y) ≠ 0) :
    x ∈ s.st.T ∧ y ∈ s.st.T :=
  (wf_proj9 hw.1 q) (x, y) h

/-! ## The potential of every operation -/

theorem potential_addTerm {s : RSt} (hw : s.WF) {t : ℕ} (ht : t ∉ s.st.T) :
    (s.addTerm t).potential = s.potential + 1 := by
  unfold RSt.potential
  rw [st_addTerm, record_addTerm, size_addTerm9 hw.1 ht, total_addTerm7 hw.2]
  omega

theorem potential_addAssertion (s : RSt) (q : Rel) {x y : ℕ} (hx : x ∈ s.st.T) (hy : y ∈ s.st.T) :
    (s.addAssertion q x y).potential = s.potential + 1 := by
  unfold RSt.potential
  rw [st_addAssertion, record_addAssertion, size_addAssertion9 q hx hy]
  omega

/-- The total of the record after a removal: the fourth's lemma on the record through the naming map. -/
theorem record_total_remove {s : RSt} {x y : ℕ} (hx : x ∈ s.st.T) (hy : y ∈ s.st.T) (q : Rel) :
    (s.remove q x y).record.total = s.record.total + 1 := by
  rw [record_remove]
  exact Seed.Fourth.total_addAssertion (s := s.record.name x) hx hy

theorem potential_remove {s : RSt} (hw : s.WF) (q : Rel) {x y : ℕ} (hp : s.st.M q (x, y) ≠ 0) :
    (s.remove q x y).potential = s.potential + 1 := by
  obtain ⟨hx, hy⟩ := mem_of_M hw q hp
  unfold RSt.potential
  have e := size_remove9 hw.1 q hp
  rw [st_remove, record_total_remove hx hy q]
  omega

/-- The total of the record after an admission: the fifth's lemma on the record through the naming map. -/
theorem record_total_admit {s : RSt} (hw : s.WF) (q : Rel) {x y : ℕ} (hl : s.L (x, y) ≠ 0) :
    (s.admitLeftover q x y).record.total + 1 = s.record.total := by
  obtain ⟨hx, hy⟩ := mem_of_L hw hl
  rw [record_admit]
  exact Seed.Fifth.total_remove (s.record.name x) hx hy hl

theorem potential_admit {s : RSt} (hw : s.WF) (q : Rel) {x y : ℕ} (hl : s.L (x, y) ≠ 0) :
    (s.admitLeftover q x y).potential + 1 = s.potential := by
  obtain ⟨hx, hy⟩ := mem_of_L hw hl
  unfold RSt.potential
  have e := record_total_admit hw q hl
  rw [st_admit, size_addAssertion9 q hx hy]
  omega

/-- The total of the record is kept by an identification: the fifth's lemma through the naming map. -/
theorem record_total_identify {s : RSt} {u v : ℕ} (hu : u ∈ s.st.T) (huv : u ≠ v) :
    (s.identify u v).record.total = s.record.total := by
  rw [record_identify]
  exact Seed.Fifth.total_identify (s.record.name u) hu huv

theorem potential_identify {s : RSt} {u v : ℕ} (hu : u ∈ s.st.T) (hv : v ∈ s.st.T) (huv : u ≠ v) :
    (s.identify u v).potential + 1 = s.potential := by
  unfold RSt.potential
  have e := size_identify9 (s := s.st) hu hv huv
  rw [st_identify, record_total_identify hu huv]
  omega

/-! ## The mass of every operation -/

theorem mass_addTerm {s : RSt} (hw : s.WF) (t : ℕ) : (s.addTerm t).mass = s.mass := by
  unfold RSt.mass
  rw [st_addTerm, record_addTerm, proj9_addTerm, proj9_addTerm, total_addTerm7 hw.1.1, total_addTerm7 hw.1.2,
    total_addTerm7 hw.2]

theorem total_proj_addAssertion_self (g : NDSt) (q : Rel) {x y : ℕ} (hx : x ∈ g.T) (hy : y ∈ g.T) :
    ((g.addAssertion q x y).proj q).total = (g.proj q).total + 1 := by
  rw [proj9_addAssertion_self]
  exact Seed.Fourth.total_addAssertion (s := (g.proj q).name x) hx hy

theorem total_proj_remove_self {g : NDSt} (hw : g.WF) (q : Rel) {x y : ℕ} (hp : g.M q (x, y) ≠ 0) :
    ((g.remove q x y).proj q).total + 1 = (g.proj q).total := by
  have hx : x ∈ g.T := ((wf_proj9 hw q) (x, y) hp).1
  have hy : y ∈ g.T := ((wf_proj9 hw q) (x, y) hp).2
  rw [proj9_remove_self]
  exact Seed.Fifth.total_remove ((g.proj q).name x) hx hy hp

theorem mass_addAssertion (s : RSt) (q : Rel) {x y : ℕ} (hx : x ∈ s.st.T) (hy : y ∈ s.st.T) :
    (s.addAssertion q x y).mass = s.mass + 1 := by
  unfold RSt.mass
  rw [st_addAssertion, record_addAssertion]
  cases q
  · rw [total_proj_addAssertion_self _ false hx hy, proj9_addAssertion_other _ (by decide) x y]
    omega
  · rw [total_proj_addAssertion_self _ true hx hy, proj9_addAssertion_other _ (by decide) x y]
    omega

theorem mass_remove {s : RSt} (hw : s.WF) (q : Rel) {x y : ℕ} (hp : s.st.M q (x, y) ≠ 0) :
    (s.remove q x y).mass = s.mass := by
  obtain ⟨hx, hy⟩ := mem_of_M hw q hp
  unfold RSt.mass
  rw [st_remove, record_total_remove hx hy q]
  cases q
  · have e := total_proj_remove_self hw.1 false hp
    have e' : ((s.st.remove false x y).proj true).total = (s.st.proj true).total :=
      congrArg NSt.total (proj9_remove_other s.st (q := false) (q' := true) (by decide) x y)
    omega
  · have e := total_proj_remove_self hw.1 true hp
    have e' : ((s.st.remove true x y).proj false).total = (s.st.proj false).total :=
      congrArg NSt.total (proj9_remove_other s.st (q := true) (q' := false) (by decide) x y)
    omega

theorem mass_admit {s : RSt} (hw : s.WF) (q : Rel) {x y : ℕ} (hl : s.L (x, y) ≠ 0) :
    (s.admitLeftover q x y).mass = s.mass := by
  obtain ⟨hx, hy⟩ := mem_of_L hw hl
  unfold RSt.mass
  have e := record_total_admit hw q hl
  rw [st_admit]
  cases q
  · rw [total_proj_addAssertion_self _ false hx hy, proj9_addAssertion_other _ (by decide) x y]
    omega
  · rw [total_proj_addAssertion_self _ true hx hy, proj9_addAssertion_other _ (by decide) x y]
    omega

theorem mass_identify {s : RSt} {u v : ℕ} (hu : u ∈ s.st.T) (huv : u ≠ v) :
    (s.identify u v).mass = s.mass := by
  unfold RSt.mass
  -- the fifth's lemma is stated on the named state; through the naming map it reads on the projection
  have e0 : ((s.st.proj false).identify u v).total = (s.st.proj false).total :=
    Seed.Fifth.total_identify ((s.st.proj false).name u) hu huv
  have e1 : ((s.st.proj true).identify u v).total = (s.st.proj true).total :=
    Seed.Fifth.total_identify ((s.st.proj true).name u) hu huv
  rw [st_identify, record_total_identify hu huv, proj9_identify, proj9_identify, e0, e1]

/-! ## The same relation, and the other -/

/-- On the ninth state: removing then adding the same assertion gives the state back. -/
theorem remove_add9 (g : NDSt) (q : Rel) {x y : ℕ} (hp : g.M q (x, y) ≠ 0) :
    (g.remove q x y).addAssertion q x y = g := by
  apply NDSt.ext
  · rfl
  · funext q' p
    by_cases hq : q' = q
    · subst hq
      by_cases he : p = (x, y)
      · subst he
        simp [NDSt.remove, NDSt.addAssertion]
        omega
      · simp [NDSt.remove, NDSt.addAssertion, he]
    · simp [NDSt.remove, NDSt.addAssertion, hq]

/-- **The same relation is the identity.**  Removing an asserted `xqy` and admitting the leftover it
records back into `q` gives the state back, record included. -/
theorem remove_admit_same (s : RSt) (q : Rel) {x y : ℕ} (hp : s.st.M q (x, y) ≠ 0) :
    (s.remove q x y).admitLeftover q x y = s := by
  apply RSt.ext
  · exact remove_add9 s.st q hp
  · funext p
    by_cases he : p = (x, y)
    · subst he
      simp [RSt.remove, RSt.admitLeftover]
    · simp [RSt.remove, RSt.admitLeftover]

/-- The removal records one leftover of its pair. -/
theorem L_remove_self (s : RSt) (q : Rel) (x y : ℕ) : (s.remove q x y).L (x, y) = s.L (x, y) + 1 := by
  simp [RSt.remove]

/-- The admission consumes one leftover of its pair. -/
theorem L_admit_self (s : RSt) (q : Rel) (x y : ℕ) : (s.admitLeftover q x y).L (x, y) = s.L (x, y) - 1 := by
  simp [RSt.admitLeftover]

theorem M_addAssertion_self (g : NDSt) (q : Rel) (x y : ℕ) :
    (g.addAssertion q x y).M q (x, y) = g.M q (x, y) + 1 := by
  simp [NDSt.addAssertion]

theorem M_addAssertion_other (g : NDSt) (q : Rel) (x y : ℕ) (p : ℕ × ℕ) :
    (g.addAssertion q x y).M (!q) p = g.M (!q) p := by
  cases q <;> simp [NDSt.addAssertion]

theorem M_remove_other (g : NDSt) (q : Rel) (x y : ℕ) (p : ℕ × ℕ) :
    (g.remove q x y).M (!q) p = g.M (!q) p := by
  cases q <;> simp [NDSt.remove]

/-- **The other relation is not the identity.**  Admitting the leftover into the other relation
raises that relation's multiplicity of the pair by one, so the outcome is a different state. -/
theorem remove_admit_other_ne (s : RSt) (q : Rel) (x y : ℕ) :
    (s.remove q x y).admitLeftover (!q) x y ≠ s := by
  intro h
  have := congrArg (fun r : RSt => r.st.M (!q) (x, y)) h
  simp only [st_admit, st_remove, M_addAssertion_self, M_remove_other] at this
  omega

/-- Nor is it the direct addition of that assertion: the record differs by one leftover. -/
theorem remove_admit_other_ne_direct (s : RSt) (q : Rel) (x y : ℕ) :
    (s.remove q x y).admitLeftover (!q) x y ≠ (s.remove q x y).addAssertion (!q) x y := by
  intro h
  have := congrArg (fun r : RSt => r.L (x, y)) h
  simp only [L_admit_self, L_addAssertion, L_remove_self] at this
  omega

/-- The two outcomes agree on the ninth state: as ninth states they are the same result. -/
theorem remove_admit_other_st (s : RSt) (q : Rel) (x y : ℕ) :
    ((s.remove q x y).admitLeftover (!q) x y).st = ((s.remove q x y).addAssertion (!q) x y).st := rfl

/-- The ninth's add-then-remove is no longer a cycle: it leaves a leftover. -/
theorem add_remove_ne (s : RSt) (q : Rel) (x y : ℕ) : (s.addAssertion q x y).remove q x y ≠ s := by
  intro h
  have := congrArg (fun r : RSt => r.L (x, y)) h
  simp only [L_remove_self, L_addAssertion] at this
  omega

/-- On the ninth state it still is one (the fourteenth's `add_remove`). -/
theorem add_remove_st (s : RSt) (q : Rel) (x y : ℕ) : ((s.addAssertion q x y).remove q x y).st = s.st :=
  Seed.Fourteenth.add_remove s.st q x y

/-- No direct addition changes the record. -/
theorem record_not_raised_by_addition (s : RSt) (q : Rel) (x y t : ℕ) :
    (s.addAssertion q x y).L = s.L ∧ (s.addTerm t).L = s.L :=
  ⟨rfl, rfl⟩

/-! ## A term added and identified away -/

/-- On a one-relation state: a fresh term added and then identified with a term that is there
leaves the state as it was. -/
theorem _root_.Seed.Seventh.NSt.identify_addTerm {m : NSt} (hw : m.WF) {c t : ℕ} (hc : c ∈ m.T)
    (ht : t ∉ m.T) : (m.addTerm t).identify c t = m := by
  have hct : c ≠ t := fun h => ht (h ▸ hc)
  apply NSt.ext
  · show (insert t m.T).erase t = m.T
    exact Finset.erase_insert ht
  · funext p
    show (∑ w ∈ ((insert t m.T) ×ˢ (insert t m.T)).filter
        (fun w => (merge c t w.1, merge c t w.2) = p), m.M w) = m.M p
    -- every pair with a non-zero multiplicity is a pair of terms of `m`, which the merge leaves alone
    have key : ∀ w ∈ ((insert t m.T) ×ˢ (insert t m.T)).filter
        (fun w => (merge c t w.1, merge c t w.2) = p), w ≠ p → m.M w = 0 := by
      intro w hw' hne
      by_contra hz
      obtain ⟨h1, h2⟩ := hw w hz
      have e1 : merge c t w.1 = w.1 := merge_of_ne (fun h => ht (h ▸ h1))
      have e2 : merge c t w.2 = w.2 := merge_of_ne (fun h => ht (h ▸ h2))
      have := (Finset.mem_filter.1 hw').2
      rw [e1, e2] at this
      exact hne (by rw [← this])
    by_cases hp : p ∈ ((insert t m.T) ×ˢ (insert t m.T)).filter
        (fun w => (merge c t w.1, merge c t w.2) = p)
    · rw [Finset.sum_eq_single_of_mem p hp]
      intro w hw' hne
      exact key w hw' hne
    · rw [Finset.sum_eq_zero]
      · by_contra hz
        obtain ⟨h1, h2⟩ := hw p (Ne.symm hz)
        apply hp
        refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩, ?_⟩
        have e1 : merge c t p.1 = p.1 := merge_of_ne (fun h => ht (h ▸ h1))
        have e2 : merge c t p.2 = p.2 := merge_of_ne (fun h => ht (h ▸ h2))
        exact Prod.ext e1 e2
      · intro w hw'
        by_cases hne : w = p
        · subst hne
          exact absurd hw' hp
        · exact key w hw' hne

/-- On a ninth state: both parts. -/
theorem identify_addTerm9 {g : NDSt} (hw : g.WF) {c t : ℕ} (hc : c ∈ g.T) (ht : t ∉ g.T) :
    (g.addTerm t).identify c t = g := by
  apply ext_proj9
  intro q
  rw [proj9_identify, proj9_addTerm]
  exact NSt.identify_addTerm (wf_proj9 hw q) hc ht

/-- On a sixteenth state: the ninth state and the record alike. -/
theorem identify_addTerm16 {s : RSt} (hw : s.WF) {c t : ℕ} (hc : c ∈ s.st.T) (ht : t ∉ s.st.T) :
    (s.addTerm t).identify c t = s := by
  apply RSt.ext
  · exact identify_addTerm9 hw.1 hc ht
  · have e : ((s.addTerm t).identify c t).record = s.record := by
      rw [record_identify, record_addTerm]
      exact NSt.identify_addTerm hw.2 hc ht
    exact congrArg NSt.M e

/-! ## The exchange of the relations -/

theorem swap16_st (s : RSt) : s.swap.st = s.st.swap := rfl
theorem swap16_L (s : RSt) : s.swap.L = s.L := rfl
theorem swap16_rec (s : RSt) : s.swap.record = s.record := rfl

theorem swap16_swap (s : RSt) : s.swap.swap = s := by
  apply RSt.ext
  · exact swap9_swap s.st
  · rfl

theorem swap16_remove (s : RSt) (q : Rel) (x y : ℕ) : (s.remove q x y).swap = s.swap.remove (!q) x y := by
  apply RSt.ext
  · exact swap9_remove s.st q x y
  · rfl

theorem swap16_admit (s : RSt) (q : Rel) (x y : ℕ) : (s.admitLeftover q x y).swap = s.swap.admitLeftover (!q) x y := by
  apply RSt.ext
  · exact swap9_addAssertion s.st q x y
  · rfl

theorem swap16_addAssertion (s : RSt) (q : Rel) (x y : ℕ) :
    (s.addAssertion q x y).swap = s.swap.addAssertion (!q) x y := by
  apply RSt.ext
  · exact swap9_addAssertion s.st q x y
  · rfl

theorem swap16_addTerm (s : RSt) (t : ℕ) : (s.addTerm t).swap = s.swap.addTerm t := rfl

theorem swap16_identify (s : RSt) (u v : ℕ) : (s.identify u v).swap = s.swap.identify u v := rfl

theorem swap16_wf {s : RSt} (hw : s.WF) : s.swap.WF := ⟨swap9_wf hw.1, hw.2⟩

theorem potential_swap (s : RSt) : s.swap.potential = s.potential := by
  unfold RSt.potential
  rw [swap16_st, swap16_rec, size9_swap]

end Seed.Sixteenth
