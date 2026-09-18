import Fourth.Cost

/-!
# Attempts, obstructions and answers under the fourth seed

An *attempt* (`Try4`) is what the seed says to attempt: adding a new term, or
adding an assertion between terms that are there — asserted already or not,
`xrx` included.  Derived here:
* an attempt is obstructed exactly when it adds some `xrx`
  (`Try4.obstructed_iff`), and an unobstructed attempt is a performed change
  (`Try4.legal_iff`); adding an assertion that is asserted already is
  unobstructed (`addAssertion_again_unobstructed`) — new to the counted seed,
  where the earlier reading C5 made it no change at all;
* the fewest-additions builds for an obstructed `xrx` (a new term `t` with `xrt`
  or `trx`) are two performed changes (`build_answer4`, `build_answer4_reverse`);
* "remove the obstruction" is not available: the would-be outcome asserts `xrx`
  and no state reached by changes does (`Reach4.xrx_still_obstructed`,
  `no_change_asserts_xrx4`), and no change lowers a multiplicity
  (`Reach4.mult_le`);
* a result can be reached by two different sequences (`two_sequences4`, the
  third derivation's witness on indicator states, and `two_sequences_counted`, a
  witness with two terms only: `arb` twice and `bra`), of the same length
  (`Reach4.length_unique`).
-/

namespace Seed.Fourth

open Seed Seed.Second Seed.Third MSt

/-- One attempted change of the fourth seed: a new term, or an assertion between
terms that are there (`xrx` allowed, asserted already or not). -/
inductive Try4 : MSt → MSt → Prop
  | addTerm (s : MSt) (t : ℕ) (ht : t ∉ s.T) : Try4 s (s.addTerm t)
  | addAssertion (s : MSt) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Try4 s (s.addAssertion x y)

/-- Every performed change is an attempt. -/
theorem Step4.toTry4 {s t : MSt} (h : Step4 s t) : Try4 s t := by
  cases h with
  | addTerm t ht => exact Try4.addTerm s t ht
  | addAssertion x y hx hy hxy => exact Try4.addAssertion s x y hx hy

/-- An attempt is a performed change, or it adds some `xrx`. -/
theorem Try4.step4_or_xrx {s t : MSt} (h : Try4 s t) :
    Step4 s t ∨ ∃ x ∈ s.T, t = s.addAssertion x x := by
  cases h with
  | addTerm t ht => exact Or.inl (Step4.addTerm s t ht)
  | addAssertion x y hx hy =>
    by_cases hxy : x = y
    · subst hxy
      exact Or.inr ⟨x, hx, rfl⟩
    · exact Or.inl (Step4.addAssertion s x y hx hy hxy)

/-- **Which attempts are obstructed.**  On a legal state an attempt makes some `xrx`
asserted exactly when it is the addition of some `xrx`. -/
theorem Try4.obstructed_iff {s t : MSt} (h : Try4 s t) (hs : s.Legal) :
    ¬ t.Legal ↔ ∃ x ∈ s.T, t = s.addAssertion x x := by
  constructor
  · intro ht
    rcases h.step4_or_xrx with h4 | hx
    · exact absurd (h4.legal hs) ht
    · exact hx
  · rintro ⟨x, _, rfl⟩
    exact adding_xrx_always_obstructed4 s x

/-- An unobstructed attempt is exactly a performed change. -/
theorem Try4.legal_iff {s t : MSt} (h : Try4 s t) (hs : s.Legal) : t.Legal ↔ Step4 s t := by
  constructor
  · intro ht
    rcases h.step4_or_xrx with h4 | ⟨x, _, rfl⟩
    · exact h4
    · exact absurd ht (adding_xrx_always_obstructed4 s x)
  · intro h4
    exact h4.legal hs

/-- Adding a term is never obstructed. -/
theorem addTerm_unobstructed4 {s : MSt} (hs : s.Legal) (t : ℕ) : (s.addTerm t).Legal := hs

/-- Adding `xry` with `x ≠ y` is never obstructed, whatever its multiplicity already
is: re-adding an asserted assertion is a performed change. -/
theorem addAssertion_again_unobstructed {s : MSt} (hs : s.Legal) {x y : ℕ} (hx : x ∈ s.T)
    (hy : y ∈ s.T) (hxy : x ≠ y) : (s.addAssertion x y).Legal ∧ Step4 s (s.addAssertion x y) :=
  ⟨(Step4.addAssertion s x y hx hy hxy).legal hs, Step4.addAssertion s x y hx hy hxy⟩

/-! ## Builds -/

/-- The build with fewest additions, `x r t` with `t` new, is two performed changes. -/
theorem build_answer4 {s : MSt} {x t : ℕ} (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach4 s ((s.addTerm t).addAssertion x t) 2 := by
  have hxt : x ≠ t := fun h => ht (h ▸ hx)
  have st1 : Step4 s (s.addTerm t) := Step4.addTerm s t ht
  have st2 : Step4 (s.addTerm t) ((s.addTerm t).addAssertion x t) :=
    Step4.addAssertion _ x t (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self t s.T) hxt
  exact Reach4.step (Reach4.step (Reach4.refl s) st1) st2

/-- The other build with fewest additions, `t r x` with `t` new. -/
theorem build_answer4_reverse {s : MSt} {x t : ℕ} (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach4 s ((s.addTerm t).addAssertion t x) 2 := by
  have hxt : t ≠ x := fun h => ht (h ▸ hx)
  have st1 : Step4 s (s.addTerm t) := Step4.addTerm s t ht
  have st2 : Step4 (s.addTerm t) ((s.addTerm t).addAssertion t x) :=
    Step4.addAssertion _ t x (Finset.mem_insert_self t s.T) (Finset.mem_insert_of_mem hx) hxt
  exact Reach4.step (Reach4.step (Reach4.refl s) st1) st2

/-! ## "Remove the obstruction" is not available -/

/-- No sequence of changes from a legal state ends in a state that asserts `xrx`: the
would-be outcome of an obstructed attempt is never reached, however the obstruction
is answered. -/
theorem no_change_asserts_xrx4 {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hs : s.Legal) (x : ℕ) :
    t.M (x, x) = 0 :=
  h.legal hs x

/-- In particular the outcome of the obstructed attempt itself is unreachable. -/
theorem xrx_outcome_unreachable4 {s : MSt} (hs : s.Legal) (x : ℕ) (n : ℕ) :
    ¬ Reach4 s (s.addAssertion x x) n := by
  intro h
  have := no_change_asserts_xrx4 h hs x
  change Function.update s.M (x, x) (s.M (x, x) + 1) (x, x) = 0 at this
  rw [Function.update_self] at this
  omega

/-! ## Two sequences to one result -/

/-- What is given, `bra` not asserted, plus a term and `bra`: reached by adding the
term first and by adding `bra` first (the third derivation's witness, on indicator
states). -/
theorem two_sequences4 :
    ∃ t1 t2 : MSt, t1 ≠ t2 ∧
      (Step4 givenA4 t1 ∧ Step4 t1 ((givenA4.addTerm 2).addAssertion 1 0)) ∧
      (Step4 givenA4 t2 ∧ Step4 t2 ((givenA4.addTerm 2).addAssertion 1 0)) := by
  refine ⟨givenA4.addTerm 2, givenA4.addAssertion 1 0, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have := congrArg MSt.T h
    simp [MSt.addTerm, MSt.addAssertion, givenA4, ofSt, givenA] at this
  · exact Step4.addTerm givenA4 2 (by simp [givenA4, ofSt, givenA])
  · exact Step4.addAssertion _ 1 0 (by simp [givenA4, ofSt, givenA, MSt.addTerm])
      (by simp [givenA4, ofSt, givenA, MSt.addTerm]) (by omega)
  · exact Step4.addAssertion givenA4 1 0 (by simp [givenA4, ofSt, givenA])
      (by simp [givenA4, ofSt, givenA]) (by omega)
  · show Step4 (givenA4.addAssertion 1 0) ((givenA4.addAssertion 1 0).addTerm 2)
    exact Step4.addTerm _ 2 (by simp [givenA4, ofSt, givenA, MSt.addAssertion])

/-- The state with `arb` twice and `bra` once is reached from what is given by adding
`arb` then `bra`, and by adding `bra` then `arb`: two different sequences, with two
terms only — a witness the third seed did not have. -/
theorem two_sequences_counted :
    ∃ t1 t2 : MSt, t1 ≠ t2 ∧
      (Step4 givenA4 t1 ∧ Step4 t1 ((givenA4.addAssertion 0 1).addAssertion 1 0)) ∧
      (Step4 givenA4 t2 ∧ Step4 t2 ((givenA4.addAssertion 0 1).addAssertion 1 0)) := by
  have h0 : (0 : ℕ) ∈ givenA4.T := by simp [givenA4, ofSt, givenA]
  have h1 : (1 : ℕ) ∈ givenA4.T := by simp [givenA4, ofSt, givenA]
  have e : (givenA4.addAssertion 1 0).addAssertion 0 1 = (givenA4.addAssertion 0 1).addAssertion 1 0 := by
    apply MSt.ext
    · rfl
    · show Function.update (Function.update givenA4.M (1, 0) (givenA4.M (1, 0) + 1)) (0, 1)
          (Function.update givenA4.M (1, 0) (givenA4.M (1, 0) + 1) (0, 1) + 1) =
        Function.update (Function.update givenA4.M (0, 1) (givenA4.M (0, 1) + 1)) (1, 0)
          (Function.update givenA4.M (0, 1) (givenA4.M (0, 1) + 1) (1, 0) + 1)
      have hne : ((1, 0) : ℕ × ℕ) ≠ (0, 1) := by decide
      rw [Function.update_of_ne hne.symm, Function.update_of_ne hne, Function.update_comm hne]
    · rfl
    · rfl
  refine ⟨givenA4.addAssertion 0 1, givenA4.addAssertion 1 0, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have := congrArg (fun s : MSt => s.M (0, 1)) h
    change Function.update givenA4.M (0, 1) (givenA4.M (0, 1) + 1) (0, 1) =
      Function.update givenA4.M (1, 0) (givenA4.M (1, 0) + 1) (0, 1) at this
    rw [Function.update_self, Function.update_of_ne (by decide)] at this
    omega
  · exact Step4.addAssertion givenA4 0 1 h0 h1 (by omega)
  · exact Step4.addAssertion _ 1 0 h1 h0 (by omega)
  · exact Step4.addAssertion givenA4 1 0 h1 h0 (by omega)
  · rw [← e]
    exact Step4.addAssertion _ 0 1 h0 h1 (by omega)

end Seed.Fourth
