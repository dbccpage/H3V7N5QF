import Second.Rename

/-!
# Answers to an obstructed change under the second seed

Derived here:
* the fewest-additions builds for an obstructed `xrx` (a new term `t` with `xrt`
  or `trx`) are two performed changes of the second seed (`build_answer3`,
  `build_answer3_reverse`); that identifying `t` back with `x` gives exactly the
  would-be outcome of adding `xrx`, and that no build does with less, are the
  first derivation's `build_gives_back`, `build_reverse_gives_back`,
  `build_needs_term_and_assertion`, which mention no change and are cited;
* "remove the obstruction" is not available: the outcome of the first
  derivation's removal answer to identifying the two named terms is unreachable
  (`removal_answer_outcome_unreachable`), and in general the obstruction to an
  identification persists (`Reach3.identify_images_obstructed`, in `Carry.lean`);
  for adding `xrx` the first derivation's `adding_xrx_always_obstructed` applies
  unchanged.
-/

namespace Seed.Second

open Seed St

/-- The build with fewest additions, `x r t` with `t` new, is two performed changes. -/
theorem build_answer3 {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach3 s ((s.addTerm t).addAssertion x t) 2 := by
  have hxt : x ≠ t := fun h => ht (h ▸ hx)
  have st1 : Step3 s (s.addTerm t) := Step3.addTerm s t ht
  have st2 : Step3 (s.addTerm t) ((s.addTerm t).addAssertion x t) :=
    Step3.addAssertion _ x t (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self t s.T) hxt
      (fun h => ht (hs.1 _ h).2)
  exact Reach3.step (Reach3.step (Reach3.refl s) st1) st2

/-- The other build with fewest additions, `t r x` with `t` new. -/
theorem build_answer3_reverse {s : St} {x t : ℕ} (hs : s.WF) (hx : x ∈ s.T) (ht : t ∉ s.T) :
    Reach3 s ((s.addTerm t).addAssertion t x) 2 := by
  have hxt : t ≠ x := fun h => ht (h ▸ hx)
  have st1 : Step3 s (s.addTerm t) := Step3.addTerm s t ht
  have st2 : Step3 (s.addTerm t) ((s.addTerm t).addAssertion t x) :=
    Step3.addAssertion _ t x (Finset.mem_insert_self t s.T) (Finset.mem_insert_of_mem hx) hxt
      (fun h => ht (hs.1 _ h).1)
  exact Reach3.step (Reach3.step (Reach3.refl s) st1) st2

/-- The first derivation answered "identify `a` and `b`" by removing `arb` and then
identifying; under the second seed that outcome is reached by no sequence of changes. -/
theorem removal_answer_outcome_unreachable {s : St} (hs : s.Legal) (hab : (s.a, s.b) ∈ s.A)
    (n : ℕ) : ¬ Reach3 s ((s.remove (s.a, s.b)).identify s.a s.b) n := by
  intro h
  have hne := h.names_apart hs hab
  apply hne
  simp [St.identify, St.remove]

end Seed.Second
