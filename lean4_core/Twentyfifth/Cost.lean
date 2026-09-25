import Twentyfifth.Blind

/-!
# The fewest changes to a result

`Cost25 A c`: `c` changes from the empty state reach some state of the result
of `A`, and no fewer do.  Derived here:
* `psi` — the twenty-second's `phi` of the assertions plus the filled triples
  — rises by at most one per change (`Step25.psi_le`): a filling raises the
  triples by one and leaves `phi`; an identification never adds a triple
  (`length_carry_le`); the four kinds raise `phi` by at most one
  (`Step.phi_le`, imported);
* from the empty state, additions reach a state asserting no pair in both
  relations (`reach_plainSt`, imported, carried by `embed_reach`) and the
  fillings follow (`reach_fill_all`);
* so **the fewest changes to a result is the twenty-third's cost of its
  assertions plus the number of its filled triples** (`cost25_eq`); with
  nothing filled it is the twenty-third's cost (`cost25_embed_iff`);
* **the twenty-third's "every change changes the cost by an odd number" fails**:
  identifying two terms of the one filled triple of `a b c` takes the cost
  from four to two (`parity_fails`);
* a change performed on a state asserting the fewest raises the cost by at most
  one (`Step25.cost_le`), and no change returns a state to its own result
  (`Step25.not_same`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

/-- The twenty-second's `phi` of the assertions, plus the filled triples. -/
def psi (A : FSt) : Nat := phi A.G + A.F.length

theorem psi_empty25 : psi empty25 = 0 := rfl

/-- **Every change raises `psi` by at most one.** -/
theorem Step25.psi_le {A B : FSt} (h : Step25 A B) : psi B ≤ psi A + 1 := by
  cases h with
  | addTerm =>
    have := (Step.addTerm A.G).phi_le
    simp only [psi, FSt.addTerm]
    omega
  | add a hx hy =>
    have := (Step.add A.G a hx hy).phi_le
    simp only [psi, FSt.add]
    omega
  | remove a ha =>
    have := (Step.remove A.G a ha).phi_le
    simp only [psi, FSt.remove]
    omega
  | identify u v hu hv huv =>
    have := (Step.identify A.G u v hu hv huv).phi_le
    have := length_carry_le A.G.n u v A.F
    simp only [psi, FSt.identify]
    omega
  | fill t _ _ _ =>
    simp only [psi, FSt.fill, List.length_cons]
    omega

theorem Reach25.psi_le {A B : FSt} {k : Nat} (h : Reach25 A B k) : psi B ≤ psi A + k := by
  induction h with
  | refl => omega
  | step _ st ih =>
    have := st.psi_le
    omega

/-- Filling the triples of a list one by one, from the last. -/
theorem reach_fill_all (G : St) :
    ∀ F : List Tri, (∀ t ∈ F, t.Within G.n ∧ t.Distinct ∧ t.norm = t) → F.Nodup →
      Reach25 ⟨G, []⟩ ⟨G, F⟩ F.length
  | [], _, _ => Reach25.refl _
  | t :: F, h, hn => by
    have r := reach_fill_all G F (fun s hs => h s (List.mem_cons_of_mem _ hs)) (List.nodup_cons.1 hn).2
    have ht := h t List.mem_cons_self
    have hnot : t.norm ∉ F := by
      rw [ht.2.2]
      exact (List.nodup_cons.1 hn).1
    have st := Step25.fill ⟨G, F⟩ t ht.1 ht.2.1 hnot
    have e : (⟨G, F⟩ : FSt).fill t = ⟨G, t :: F⟩ := by
      simp only [FSt.fill, ht.2.2]
    rw [e] at st
    exact Reach25.step r st

/-- From the empty state, the state with the plain part of `A`'s assertions and `A`'s filled triples, in
`psi A` changes. -/
theorem reach_build {A : FSt} (hA : A.WF) : Reach25 empty25 ⟨A.G.plainSt, A.F⟩ (psi A) := by
  have r1 : Reach25 (embed empty) (embed A.G.plainSt) (phi A.G) := embed_reach (reach_plainSt hA.1).reach
  have r2 := reach_fill_all A.G.plainSt A.F (fun t ht => hA.2.1 t ht) hA.2.2
  exact Reach25.trans r1 r2

theorem same_build (A : FSt) : Same25 ⟨A.G.plainSt, A.F⟩ A :=
  ⟨Same.same3 (same_plainSt A.G).symm, List.Perm.refl _⟩

/-- `c` is the fewest changes from the empty state to a state of the result of `A`. -/
def Cost25 (A : FSt) (c : Nat) : Prop :=
  (∃ B, Same25 B A ∧ Reach25 empty25 B c) ∧ ∀ B k, Same25 B A → Reach25 empty25 B k → c ≤ k

theorem Cost25.unique {A : FSt} {c c' : Nat} (h : Cost25 A c) (h' : Cost25 A c') : c = c' := by
  obtain ⟨⟨B, s, r⟩, lo⟩ := h
  obtain ⟨⟨B', s', r'⟩, lo'⟩ := h'
  have a := lo B' c' s' r'
  have b := lo' B c s r
  omega

/-- The cost is a mark of the result. -/
theorem Cost25.congr {A A' : FSt} (h : Same25 A A') {c : Nat} : Cost25 A c ↔ Cost25 A' c := by
  constructor
  · rintro ⟨⟨B, s, r⟩, lo⟩
    exact ⟨⟨B, s.trans h, r⟩, fun C k s' r' => lo C k (s'.trans h.symm) r'⟩
  · rintro ⟨⟨B, s, r⟩, lo⟩
    exact ⟨⟨B, s.trans h.symm, r⟩, fun C k s' r' => lo C k (s'.trans h) r'⟩

/-- **The fewest changes to a result: the twenty-third's cost of its assertions plus its filled triples.** -/
theorem cost25_eq {A : FSt} (hA : A.WF) {c : Nat} (h : Cost3 A.G c) : Cost25 A (c + A.F.length) := by
  obtain ⟨⟨H, hH, s, e⟩, lo⟩ := cost3_iff.1 h
  refine ⟨⟨⟨H.plainSt, A.F⟩, ⟨(Same.same3 (same_plainSt H).symm).trans s, List.Perm.refl _⟩, ?_⟩, ?_⟩
  · have hn : H.plainSt.n = A.G.n := s.n
    have r1 : Reach25 (embed empty) (embed H.plainSt) (phi H) := embed_reach (reach_plainSt hH).reach
    have r2 := reach_fill_all H.plainSt A.F (fun t ht => by rw [hn]; exact hA.2.1 t ht) hA.2.2
    have := Reach25.trans r1 r2
    rw [e] at this
    exact this
  · intro B k sB r
    have hB := r.wf empty25_wf
    have a := lo B.G hB.1 sB.1
    have b := r.psi_le
    have l := sB.2.length_eq
    rw [psi_empty25] at b
    simp only [psi] at b
    omega

/-- A sequence of changes read on the assertions: the fillings dropped, no longer. -/
theorem Reach25.proj {A B : FSt} {k : Nat} (h : Reach25 A B k) : ∃ j, j ≤ k ∧ Reach A.G B.G j := by
  induction h with
  | refl => exact ⟨0, Nat.le_refl _, Reach.refl _⟩
  | step _ st ih =>
    obtain ⟨j, hj, rj⟩ := ih
    cases st with
    | addTerm => exact ⟨j + 1, by omega, Reach.step rj (Step.addTerm _)⟩
    | add a hx hy => exact ⟨j + 1, by omega, Reach.step rj (Step.add _ a hx hy)⟩
    | remove a ha => exact ⟨j + 1, by omega, Reach.step rj (Step.remove _ a ha)⟩
    | identify u v hu hv huv => exact ⟨j + 1, by omega, Reach.step rj (Step.identify _ u v hu hv huv)⟩
    | fill t _ _ _ => exact ⟨j, by omega, rj⟩

theorem perm_nil_eq {l : List Tri} (h : l.Perm []) : l = [] := by
  cases l with
  | nil => rfl
  | cons t l' =>
    have := h.length_eq
    simp at this

/-- **With nothing filled, the cost is the twenty-third's.** -/
theorem cost25_embed_iff {G : St} (hG : G.WF) {c : Nat} : Cost25 (embed G) c ↔ Cost3 G c := by
  constructor
  · rintro ⟨⟨B, sB, r⟩, lo⟩
    have hF : B.F = [] := perm_nil_eq sB.2
    obtain ⟨j, hj, rj⟩ := r.proj
    have hc : c ≤ j := lo (embed B.G) j ⟨sB.1, List.Perm.refl _⟩ (embed_reach rj)
    have ej : j = c := by omega
    rw [ej] at rj
    refine ⟨⟨B.G, sB.1, rj⟩, fun H k s rH => ?_⟩
    exact lo (embed H) k ⟨s, List.Perm.refl _⟩ (embed_reach rH)
  · intro h
    have := cost25_eq (embed_wf hG) h
    exact this

/-- `n` terms asserting nothing cost `n` changes in the twenty-third. -/
theorem cost3_nothing (n : Nat) : Cost3 ⟨n, []⟩ n := by
  refine cost3_iff.2 ⟨⟨⟨n, []⟩, nothing_wf n, Same3.refl _, rfl⟩, fun H _ s => ?_⟩
  have e : H.n = n := s.n
  simp only [phi]
  omega

/-- `a b c`, nothing asserted, `a b c` filled. -/
def oneFilled : FSt := ⟨⟨3, []⟩, [⟨0, 1, 2⟩]⟩

/-- `a b c`, nothing asserted, `a c b` filled. -/
def oneFilledOther : FSt := ⟨⟨3, []⟩, [⟨0, 2, 1⟩]⟩

theorem oneFilled_wf : oneFilled.WF := by
  refine ⟨nothing_wf 3, fun t ht => ?_, by decide⟩
  simp only [oneFilled, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  exact ⟨by decide, by decide, rfl⟩

theorem oneFilledOther_wf : oneFilledOther.WF := by
  refine ⟨nothing_wf 3, fun t ht => ?_, by decide⟩
  simp only [oneFilledOther, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  exact ⟨by decide, by decide, rfl⟩

theorem cost_oneFilled : Cost25 oneFilled 4 := cost25_eq oneFilled_wf (cost3_nothing 3)

theorem cost_oneFilledOther : Cost25 oneFilledOther 4 := cost25_eq oneFilledOther_wf (cost3_nothing 3)

/-- **The twenty-third's parity of the cost fails here**: identifying `a` and `b` in `a b c` with `a b c`
filled is one change, and takes the cost from four to two — the filled triple is left without three
different terms and dropped. -/
theorem parity_fails :
    Step25 oneFilled (embed ⟨2, []⟩) ∧ Cost25 oneFilled 4 ∧ Cost25 (embed ⟨2, []⟩) 2 := by
  have st := Step25.identify oneFilled 0 1 (by decide) (by decide) (by decide)
  have e : oneFilled.identify 0 1 = embed ⟨2, []⟩ := rfl
  rw [e] at st
  exact ⟨st, cost_oneFilled, (cost25_embed_iff (nothing_wf 2)).2 (cost3_nothing 2)⟩

/-- The cost is at most `psi` of any well-formed state of the result. -/
theorem Cost25.le_psi {A : FSt} (hA : A.WF) {c : Nat} (h : Cost25 A c) : c ≤ psi A :=
  h.2 _ _ (same_build A) (reach_build hA)

/-- **A change performed on a state asserting the fewest raises the cost by at most one.** -/
theorem Step25.cost_le {A B : FSt} (st : Step25 A B) (hA : A.WF) (_h : Cost25 A (psi A)) {c' : Nat}
    (h' : Cost25 B c') : c' ≤ psi A + 1 := by
  have a := h'.le_psi (st.wf hA)
  have b := st.psi_le
  omega

/-- **No change returns a state to its own result.** -/
theorem Step25.not_same {A B : FSt} (st : Step25 A B) (hA : A.WF) : ¬ Same25 A B := by
  intro s
  cases st with
  | addTerm =>
    have := s.n
    simp only [FSt.addTerm, St.addTerm] at this
    omega
  | add a hx hy => exact Step.not_same3 (Step.add A.G a hx hy) hA.1 s.1
  | remove a ha => exact Step.not_same3 (Step.remove A.G a ha) hA.1 s.1
  | identify u v hu hv huv =>
    have := s.n
    simp only [FSt.identify, St.identify] at this
    omega
  | fill t _ _ _ =>
    have := s.2.length_eq
    simp only [FSt.fill, List.length_cons] at this
    omega

end Twentyfifth
