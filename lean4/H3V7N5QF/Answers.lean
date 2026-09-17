import H3V7N5QF.Paths

/-!
# Answers to an obstructed change reach nothing new

Derived here:
* removing the obstruction before an identification gives the same state as
  performing the identification and then removing the `xrx` it made
  (`remove_obstruction_first_or_last`), and it is a sequence of performed
  changes (`remove_answer_one_way`, `remove_answer_two_way`);
* the fewest-additions build for an obstructed `xrx` — a new term `t` and `xrt`
  (or `trx`) — is a sequence of two performed changes (`build_answer`,
  `build_answer_reverse`), and identifying `t` back with `x` gives exactly the
  would-be outcome of adding `xrx` (`build_gives_back`, `build_reverse_gives_back`);
* no build does with less: a legal state whose terms, replaced by a map that
  keeps the old terms, give `xrx`, has an assertion that was not there and
  that mentions a term that was not there (`build_needs_term_and_assertion`).
-/

namespace Seed

open St

/-- Removing `urv` and `vru` first and then identifying, or identifying and then
removing the `uru` that results: the same state. -/
theorem remove_obstruction_first_or_last {s : St} (hs : s.Legal) (u v : ℕ) :
    ((s.remove (u, v)).remove (v, u)).identify u v = (s.identify u v).remove (u, u) := by
  apply St.ext
  · rfl
  · ext p
    simp only [St.identify, St.remove, Finset.mem_image, Finset.mem_erase, Prod.map]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hvu, huv, hq⟩, rfl⟩
      refine ⟨?_, (x, y), hq, rfl⟩
      intro he
      simp only [Prod.mk.injEq] at he
      have hxy : x ≠ y := by
        rintro rfl
        exact hs _ hq
      rcases merge_eq_merge hxy (he.1.trans he.2.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv rfl
      · exact hvu rfl
    · rintro ⟨hne, ⟨x, y⟩, hq, rfl⟩
      refine ⟨(x, y), ⟨?_, ?_, hq⟩, rfl⟩
      · rintro he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hne (by simp)
      · rintro he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact hne (by simp)
  · rfl
  · rfl

/-- The answer "remove the obstruction" to an identification obstructed by `urv`
alone is two performed changes. -/
theorem remove_answer_one_way {s : St} {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T)
    (hne : u ≠ v) (huv : (u, v) ∈ s.A) (hvu : (v, u) ∉ s.A) :
    Reach s ((s.remove (u, v)).identify u v) 2 := by
  have st1 : Step s (s.remove (u, v)) := Step.remove s (u, v) huv
  have st2 : Step (s.remove (u, v)) ((s.remove (u, v)).identify u v) :=
    Step.identify _ u v hu hv hne (Finset.notMem_erase _ _)
      (fun h => hvu (Finset.mem_of_mem_erase h))
  exact Reach.step (Reach.step (Reach.refl s) st1) st2

/-- The answer "remove the obstruction" to an identification obstructed by `urv`
and `vru` is three performed changes. -/
theorem remove_answer_two_way {s : St} {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T)
    (hne : u ≠ v) (huv : (u, v) ∈ s.A) (hvu : (v, u) ∈ s.A) :
    Reach s (((s.remove (u, v)).remove (v, u)).identify u v) 3 := by
  have st1 : Step s (s.remove (u, v)) := Step.remove s (u, v) huv
  have hvu' : (v, u) ∈ (s.remove (u, v)).A :=
    Finset.mem_erase.2 ⟨fun h => hne (Prod.mk.inj h).2, hvu⟩
  have st2 : Step (s.remove (u, v)) ((s.remove (u, v)).remove (v, u)) :=
    Step.remove _ (v, u) hvu'
  have st3 : Step ((s.remove (u, v)).remove (v, u))
      (((s.remove (u, v)).remove (v, u)).identify u v) :=
    Step.identify _ u v hu hv hne
      (fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h))
      (Finset.notMem_erase _ _)
  exact Reach.step (Reach.step (Reach.step (Reach.refl s) st1) st2) st3

/-- The build with fewest additions, `x r t` with `t` new, is two performed changes. -/
theorem build_answer {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach s ((s.addTerm t).addAssertion x t) 2 := by
  have hxt : x ≠ t := fun h => ht (h ▸ hx)
  have st1 : Step s (s.addTerm t) := Step.addTerm s t ht
  have st2 : Step (s.addTerm t) ((s.addTerm t).addAssertion x t) :=
    Step.addAssertion _ x t (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self t s.T) hxt
      (fun h => ht (hs.1 _ h).2)
  exact Reach.step (Reach.step (Reach.refl s) st1) st2

/-- The other build with fewest additions, `t r x` with `t` new. -/
theorem build_answer_reverse {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach s ((s.addTerm t).addAssertion t x) 2 := by
  have hxt : t ≠ x := fun h => ht (h ▸ hx)
  have st1 : Step s (s.addTerm t) := Step.addTerm s t ht
  have st2 : Step (s.addTerm t) ((s.addTerm t).addAssertion t x) :=
    Step.addAssertion _ t x (Finset.mem_insert_self t s.T) (Finset.mem_insert_of_mem hx) hxt
      (fun h => ht (hs.1 _ h).1)
  exact Reach.step (Reach.step (Reach.refl s) st1) st2

theorem image_merge_of_wf {s : St} (hs : s.WF) {x t : ℕ} (ht : t ∉ s.T) :
    s.A.image (Prod.map (merge x t) (merge x t)) = s.A := by
  have hfix : ∀ p ∈ s.A, Prod.map (merge x t) (merge x t) p = p := by
    rintro ⟨y, z⟩ hp
    have hy : y ≠ t := fun h => ht (h ▸ (hs.1 _ hp).1)
    have hz : z ≠ t := fun h => ht (h ▸ (hs.1 _ hp).2)
    simp [Prod.map, merge_of_ne hy, merge_of_ne hz]
  ext p
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [hfix q hq]
    exact hq
  · intro hp
    exact ⟨p, hp, hfix p hp⟩

/-- Identifying the built term back with `x` gives exactly the would-be outcome of
adding `xrx`: the build stands for the obstructed change. -/
theorem build_gives_back {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T) (ht : t ∉ s.T) :
    ((s.addTerm t).addAssertion x t).identify x t = s.addAssertion x x := by
  have hxt : x ≠ t := fun h => ht (h ▸ hx)
  have ha : s.a ≠ t := fun h => ht (h ▸ hs.2.1)
  have hb : s.b ≠ t := fun h => ht (h ▸ hs.2.2)
  apply St.ext
  · simp [St.identify, St.addAssertion, St.addTerm, Finset.erase_insert ht]
  · simp only [St.identify, St.addAssertion, St.addTerm, Finset.image_insert,
      image_merge_of_wf hs ht]
    simp [Prod.map]
  · simp [St.identify, St.addAssertion, St.addTerm, merge_of_ne ha]
  · simp [St.identify, St.addAssertion, St.addTerm, merge_of_ne hb]

theorem build_reverse_gives_back {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T)
    (ht : t ∉ s.T) : ((s.addTerm t).addAssertion t x).identify x t = s.addAssertion x x := by
  have hxt : x ≠ t := fun h => ht (h ▸ hx)
  have ha : s.a ≠ t := fun h => ht (h ▸ hs.2.1)
  have hb : s.b ≠ t := fun h => ht (h ▸ hs.2.2)
  apply St.ext
  · simp [St.identify, St.addAssertion, St.addTerm, Finset.erase_insert ht]
  · simp only [St.identify, St.addAssertion, St.addTerm, Finset.image_insert,
      image_merge_of_wf hs ht]
    simp [Prod.map]
  · simp [St.identify, St.addAssertion, St.addTerm, merge_of_ne ha]
  · simp [St.identify, St.addAssertion, St.addTerm, merge_of_ne hb]

/-- **No build with less.**  If replacing terms by `q` (which keeps every old term)
turns a legal `g` into something that asserts `xrx`, then `g` asserts something
that `s` did not, mentioning a term that `s` did not have. -/
theorem build_needs_term_and_assertion {s g : St} (hs : s.WF) (hg : g.Legal) (q : ℕ → ℕ)
    (hq : ∀ t ∈ s.T, q t = t) {x : ℕ}
    (himg : (x, x) ∈ g.A.image (Prod.map q q)) :
    ∃ p ∈ g.A, p ∉ s.A ∧ (p.1 ∉ s.T ∨ p.2 ∉ s.T) := by
  obtain ⟨⟨y, z⟩, hp, he⟩ := Finset.mem_image.1 himg
  simp only [Prod.map, Prod.mk.injEq] at he
  have hyz : y ≠ z := by
    rintro rfl
    exact hg _ hp
  have hout : y ∉ s.T ∨ z ∉ s.T := by
    by_contra hcon
    push Not at hcon
    exact hyz ((hq y hcon.1).symm.trans (he.1.trans (he.2.symm.trans (hq z hcon.2))))
  refine ⟨(y, z), hp, fun hmem => ?_, hout⟩
  rcases hout with h | h
  · exact h (hs.1 _ hmem).1
  · exact h (hs.1 _ hmem).2

end Seed
