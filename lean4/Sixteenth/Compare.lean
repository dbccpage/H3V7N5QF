import Sixteenth.Reach

/-!
# What survives once the record feeds back

The task's rule 5 asks, for every result of an earlier derivation that is used,
whether its proof still holds from the sixteenth seed — in particular which of
the ninth's collapses and independence survive, and which of the fourteenth's
"by construction" claims about the leftover survive once the leftover can be
admitted.  This file states the answers in Lean through the two maps `toNDSt`
(the record forgotten) and `ofRSt` (a ninth state with an empty record).

From the ninth —
* **the results**: the ninth's results are exactly the results with an empty
  record (`results_ninth_iff16`), at the ninth's round (`ninth_round_survives`);
  the sixteenth has results no ninth sequence reaches (`leftOne_is_new`);
* **the cost**: the size survives on the empty-record results and only there
  (`fewest_changes16_of_empty_record`, `ninth_cost_fails_off_empty_record`);
* **the criterion**: the has-a-term criterion does not survive
  (`has_term_criterion_fails16`); what replaces it is the mass, which is
  carried and never lost (`Reach16.mass_le`), so reachability is one-way
  again (`one_way16`);
* **the cycle**: the ninth's add-then-remove is not a cycle here
  (`add_remove_ne`); a term added and identified away is (`cycle2_16`), and so
  is a removal followed by the admission of its leftover (`cycle2_assert16`);
* **the exchange** of the relations is still a symmetry (`exchange_symmetry16`).

From the fourteenth —
* **leftover of `r` is leftover of `s`** survives and gains force: the record
  of a removal does not depend on the relation (`record_names_no_relation`),
  so a leftover left by a removal in `r` is admitted into `s`
  (`r_leftover_admitted_into_s`);
* **"clearing leftover is not one of the four kinds"** fails: an admission
  clears a leftover and is a change — of the fourth kind, adding an assertion
  (`clearing_is_a_kind16`, `Step16.proj` on it);
* **"leftover is not an assertion"** survives only of an *unadmitted*
  leftover: the admitted one is the assertion it added
  (`admitted_leftover_is_the_assertion`);
* **"leftover is not a third multiplicity"** does not survive as stated: the
  record is a count per pair carried by the state (`RSt.L`), but it is not
  raised by any addition (`record_not_raised_by_addition`) and it is not a
  third relation: only a removal raises it and only an admission lowers it.
-/

namespace Seed.Sixteenth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth Seed.Ninth NDSt RSt

/-! ## From the ninth -/

/-- Every result of the ninth is a result of the sixteenth with an empty record, at the same round,
and in no fewer changes. -/
theorem ninth_round_survives {g : NDSt} {n : ℕ} (h : Reach9 empty9 g n) :
    Reach16 empty16 g.ofRSt g.size ∧ ∀ m, Reach16 empty16 g.ofRSt m → g.size ≤ m :=
  fewest_changes16_of_empty_record (h.wf empty9_wf)

/-- The sixteenth has a result no ninth sequence reaches: the one-term state with one leftover
recorded is not the embedding of any ninth state. -/
theorem leftOne_is_new : Reach16 empty16 leftOne 3 ∧ ∀ g : NDSt, leftOne ≠ g.ofRSt := by
  refine ⟨ninth_cost_fails_off_empty_record.2.1, fun g h => ?_⟩
  have := congrArg (fun r : RSt => r.L (0, 0)) h
  simp [leftOne] at this

/-- **The exchange of the relations is a symmetry of the results, the cost and the mass.** -/
theorem exchange_symmetry16 {g : RSt} {n : ℕ} (h : Reach16 empty16 g n) :
    Reach16 empty16 g.swap n ∧ g.swap.potential = g.potential ∧ g.swap.mass = g.mass := by
  refine ⟨result16_swap h, potential_swap g, ?_⟩
  unfold RSt.mass
  rw [swap16_st, swap16_rec, proj9_swap, proj9_swap]
  show (g.st.proj true).total + (g.st.proj false).total + g.record.total = _
  omega

/-! ## From the fourteenth -/

/-- The record left by a removal does not depend on the relation removed from. -/
theorem record_names_no_relation (s : RSt) (x y : ℕ) : (s.remove false x y).L = (s.remove true x y).L := rfl

/-- Two terms with `0 r 1` and `0 s 1` each once, embedded. -/
def twoBoth16 : RSt := Seed.Fourteenth.twoBoth.ofRSt

/-- A leftover left by a removal in `r` is admitted into `s`: a change of the sixteenth. -/
theorem r_leftover_admitted_into_s :
    Step16 twoBoth16 (twoBoth16.remove false 0 1) ∧
      Step16 (twoBoth16.remove false 0 1) ((twoBoth16.remove false 0 1).admitLeftover true 0 1) := by
  refine ⟨Step16.remove twoBoth16 false 0 1 (by simp [twoBoth16, Seed.Fourteenth.twoBoth]), ?_⟩
  exact Step16.admitLeftover _ true 0 1 (by simp [RSt.remove])

/-- Admitting a leftover clears it and is a change of the fourth kind (adding an assertion): the
fourteenth's "clearing leftover is not one of the four kinds" does not survive. -/
theorem clearing_is_a_kind16 {s : RSt} (hw : s.WF) (q : Rel) {x y : ℕ} (hl : s.L (x, y) ≠ 0) :
    Step16 s (s.admitLeftover q x y) ∧ (s.admitLeftover q x y).L (x, y) + 1 = s.L (x, y) ∧
      Step9 s.st (s.st.addAssertion q x y) := by
  obtain ⟨hx, hy⟩ := mem_of_L hw hl
  refine ⟨Step16.admitLeftover s q x y hl, ?_, Step9.addAssertion s.st q x y hx hy⟩
  rw [L_admit_self]
  omega

/-- An admitted leftover is the assertion it added: the multiplicity rises by one as the record
falls by one. -/
theorem admitted_leftover_is_the_assertion (s : RSt) (q : Rel) (x y : ℕ) :
    (s.admitLeftover q x y).st.M q (x, y) = s.st.M q (x, y) + 1 ∧ (s.admitLeftover q x y).L (x, y) = s.L (x, y) - 1 :=
  ⟨M_addAssertion_self s.st q x y, L_admit_self s q x y⟩

/-- Only a removal raises the record of a pair, and only an admission lowers it: a term, a direct
assertion and an identification of two other terms leave the record of the pair as it is. -/
theorem record_moved_only_by_removal_and_admission (s : RSt) (q : Rel) (x y t : ℕ) :
    (s.addTerm t).L (x, y) = s.L (x, y) ∧ (s.addAssertion q x y).L (x, y) = s.L (x, y) ∧
      (s.remove q x y).L (x, y) = s.L (x, y) + 1 ∧ (s.admitLeftover q x y).L (x, y) = s.L (x, y) - 1 :=
  ⟨rfl, rfl, L_remove_self s q x y, L_admit_self s q x y⟩

end Seed.Sixteenth
