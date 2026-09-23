import H3V7N5QF.Paths

/-!
# Identification in one chosen assertion

A partial identification rewrites one asserted pair and leaves the terms in
place. The base identification erases a term. No sequence of partial
identifications, removals, additions of assertions, or additions of terms
reaches the one-term state from what is given.
-/

namespace Seed.Nineteenth

open Seed

/-- Write `survivor` for `u` and for `v` in one term of one pair. -/
def subTerm (u v survivor t : ℕ) : ℕ :=
  if t = u ∨ t = v then survivor else t

/-- Rewrite one pair. -/
def rewritePair (p : ℕ × ℕ) (u v survivor : ℕ) : ℕ × ℕ :=
  (subTerm u v survivor p.1, subTerm u v survivor p.2)

/-- The outcome of rewriting one asserted pair. The terms stay. -/
def performPartial (s : St) (p : ℕ × ℕ) (u v survivor : ℕ) : St :=
  ⟨s.T, insert (rewritePair p u v survivor) (s.A.erase p), s.a, s.b⟩

theorem performPartial_terms (s : St) (p : ℕ × ℕ) (u v survivor : ℕ) :
    (performPartial s p u v survivor).T = s.T := rfl

/-- A pair that already names both terms becomes a loop. -/
theorem cooccur_is_loop (u v survivor : ℕ) :
    rewritePair (u, v) u v survivor = (survivor, survivor) := by
  simp [rewritePair, subTerm]

/-- Two terms, and one assertion that names only the first. -/
def side : St := ⟨{0, 1, 2}, {(0, 2)}, 0, 1⟩

theorem side_partial_eq :
    performPartial side (0, 2) 0 1 1 = ⟨{0, 1, 2}, {(1, 2)}, 0, 1⟩ := by
  decide

theorem side_partial_legal : (performPartial side (0, 2) 0 1 1).Legal := by
  intro x hx
  rw [side_partial_eq] at hx
  simp only [Finset.mem_singleton, Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, hx⟩
  omega

theorem side_not_identify :
    performPartial side (0, 2) 0 1 1 ≠ side.identify 0 1 := by
  decide

theorem identify_smaller : (givenA.identify 0 1).T.card < givenA.T.card := by
  decide

/-- A change of this seed. Adding a term may repeat a term; the count still does not fall. -/
inductive PStep : St → St → Prop
  | rewriteOne (s : St) (p : ℕ × ℕ) (u v survivor : ℕ) : PStep s (performPartial s p u v survivor)
  | addTerm (s : St) (t : ℕ) : PStep s (s.addTerm t)
  | addAssertion (s : St) (x y : ℕ) : PStep s (s.addAssertion x y)
  | remove (s : St) (p : ℕ × ℕ) : PStep s (s.remove p)

inductive PReach : St → St → Prop
  | refl (s : St) : PReach s s
  | step {s t u : St} : PReach s t → PStep t u → PReach s u

theorem PStep.card_ge {s t : St} (h : PStep s t) : s.T.card ≤ t.T.card := by
  cases h with
  | rewriteOne p u v survivor =>
    rw [performPartial_terms]
  | addTerm t =>
    exact Finset.card_le_card (Finset.subset_insert t s.T)
  | addAssertion x y =>
    simp [St.addAssertion]
  | remove p =>
    simp [St.remove]

theorem PReach.card_ge {s t : St} (h : PReach s t) : s.T.card ≤ t.T.card := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ st ih => exact Nat.le_trans ih st.card_ge

theorem givenA_card : givenA.T.card = 2 := by decide

theorem oneTerm_card : oneTerm.T.card = 1 := by decide

/-- The base's one-term result is not reached by any sequence of these changes. -/
theorem oneTerm_unreachable : ¬ PReach givenA oneTerm := by
  intro h
  have hle := h.card_ge
  rw [givenA_card, oneTerm_card] at hle
  omega

end Seed.Nineteenth
