import Third.Rename

/-!
# Attempts, obstructions and answers under the third seed

An *attempt* (`Try2`) is what the seed says to attempt: adding a new term, or
adding a new assertion between terms that are there — `xrx` included.  Derived
here:
* an attempt is obstructed exactly when it adds some `xrx` (`Try2.obstructed_iff`),
  and an unobstructed attempt is a performed change (`Try2.legal_iff`);
* the fewest-additions builds for an obstructed `xrx` (a new term `t` with `xrt`
  or `trx`) are two performed changes of this seed (`build_answer2`,
  `build_answer2_reverse`); that reading the added term as `x` gives exactly the
  would-be outcome, and that no build does with less, are the first
  derivation's `build_gives_back`, `build_reverse_gives_back`,
  `build_needs_term_and_assertion`, which mention no change and are cited;
* "remove the obstruction" is not available: the would-be outcome asserts `xrx`
  and no state reached by changes does (`Reach2.xrx_still_obstructed`,
  `no_change_asserts_xrx`), and no change is a removal (`Step2.ne_remove`);
* a result can be reached by two different sequences (`two_sequences`), of the
  same length (`Reach2.length_unique`).
-/

namespace Seed.Third

open Seed Seed.Second St

/-- One attempted change of the third seed: a new term, or a new assertion between
terms that are there (`xrx` allowed). -/
inductive Try2 : St → St → Prop
  | addTerm (s : St) (t : ℕ) (ht : t ∉ s.T) : Try2 s (s.addTerm t)
  | addAssertion (s : St) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) (hnew : (x, y) ∉ s.A) :
      Try2 s (s.addAssertion x y)

/-- Every performed change is an attempt. -/
theorem Step2.toTry2 {s t : St} (h : Step2 s t) : Try2 s t := by
  cases h with
  | addTerm t ht => exact Try2.addTerm s t ht
  | addAssertion x y hx hy hxy hnew => exact Try2.addAssertion s x y hx hy hnew

/-- An attempt is a performed change, or it adds some `xrx`. -/
theorem Try2.step2_or_xrx {s t : St} (h : Try2 s t) :
    Step2 s t ∨ ∃ x ∈ s.T, t = s.addAssertion x x := by
  cases h with
  | addTerm t ht => exact Or.inl (Step2.addTerm s t ht)
  | addAssertion x y hx hy hnew =>
    by_cases hxy : x = y
    · subst hxy
      exact Or.inr ⟨x, hx, rfl⟩
    · exact Or.inl (Step2.addAssertion s x y hx hy hxy hnew)

/-- **Which attempts are obstructed.**  On a legal state an attempt makes some `xrx`
asserted exactly when it is the addition of some `xrx`. -/
theorem Try2.obstructed_iff {s t : St} (h : Try2 s t) (hs : s.Legal) :
    ¬ t.Legal ↔ ∃ x ∈ s.T, t = s.addAssertion x x := by
  constructor
  · intro ht
    rcases h.step2_or_xrx with h2 | hx
    · exact absurd (h2.legal hs) ht
    · exact hx
  · rintro ⟨x, _, rfl⟩
    exact adding_xrx_always_obstructed s x

/-- An unobstructed attempt is exactly a performed change. -/
theorem Try2.legal_iff {s t : St} (h : Try2 s t) (hs : s.Legal) : t.Legal ↔ Step2 s t := by
  constructor
  · intro ht
    rcases h.step2_or_xrx with h2 | ⟨x, _, rfl⟩
    · exact h2
    · exact absurd ht (adding_xrx_always_obstructed s x)
  · intro h2
    exact h2.legal hs

/-- Adding a term is never obstructed (first derivation's `addTerm_legal`). -/
theorem addTerm_unobstructed {s : St} (hs : s.Legal) (t : ℕ) : (s.addTerm t).Legal :=
  addTerm_legal hs t

/-! ## Builds -/

/-- The build with fewest additions, `x r t` with `t` new, is two performed changes. -/
theorem build_answer2 {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach2 s ((s.addTerm t).addAssertion x t) 2 := by
  have hxt : x ≠ t := fun h => ht (h ▸ hx)
  have st1 : Step2 s (s.addTerm t) := Step2.addTerm s t ht
  have st2 : Step2 (s.addTerm t) ((s.addTerm t).addAssertion x t) :=
    Step2.addAssertion _ x t (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self t s.T) hxt
      (fun h => ht (hs.1 _ h).2)
  exact Reach2.step (Reach2.step (Reach2.refl s) st1) st2

/-- The other build with fewest additions, `t r x` with `t` new. -/
theorem build_answer2_reverse {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach2 s ((s.addTerm t).addAssertion t x) 2 := by
  have hxt : t ≠ x := fun h => ht (h ▸ hx)
  have st1 : Step2 s (s.addTerm t) := Step2.addTerm s t ht
  have st2 : Step2 (s.addTerm t) ((s.addTerm t).addAssertion t x) :=
    Step2.addAssertion _ t x (Finset.mem_insert_self t s.T) (Finset.mem_insert_of_mem hx) hxt
      (fun h => ht (hs.1 _ h).1)
  exact Reach2.step (Reach2.step (Reach2.refl s) st1) st2

/-! ## "Remove the obstruction" is not available -/

/-- No sequence of changes from a legal state ends in a state that asserts `xrx`: the
would-be outcome of an obstructed attempt is never reached, however the obstruction
is answered. -/
theorem no_change_asserts_xrx {s t : St} {n : ℕ} (h : Reach2 s t n) (hs : s.Legal) (x : ℕ) :
    (x, x) ∉ t.A :=
  h.legal hs x

/-- In particular the outcome of the obstructed attempt itself is unreachable. -/
theorem xrx_outcome_unreachable {s : St} (hs : s.Legal) (x : ℕ) (n : ℕ) :
    ¬ Reach2 s (s.addAssertion x x) n :=
  fun h => no_change_asserts_xrx h hs x (by simp [St.addAssertion])

/-! ## Two sequences to one result -/

/-- What is given, `bra` not asserted, plus a term `c` and `bra`: reached by adding the
term first and by adding `bra` first — two different sequences of the same length. -/
theorem two_sequences :
    ∃ t1 t2 : St, t1 ≠ t2 ∧
      (Step2 givenA t1 ∧ Step2 t1 ((givenA.addTerm 2).addAssertion 1 0)) ∧
      (Step2 givenA t2 ∧ Step2 t2 ((givenA.addTerm 2).addAssertion 1 0)) := by
  refine ⟨givenA.addTerm 2, givenA.addAssertion 1 0, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · decide
  · exact Step2.addTerm givenA 2 (by decide)
  · exact Step2.addAssertion _ 1 0 (by simp [givenA, St.addTerm]) (by simp [givenA, St.addTerm])
      (by omega) (by simp [givenA, St.addTerm])
  · exact Step2.addAssertion givenA 1 0 (by simp [givenA]) (by simp [givenA]) (by omega)
      (by simp [givenA])
  · show Step2 (givenA.addAssertion 1 0) ((givenA.addAssertion 1 0).addTerm 2)
    exact Step2.addTerm _ 2 (by simp [givenA, St.addAssertion])

end Seed.Third
