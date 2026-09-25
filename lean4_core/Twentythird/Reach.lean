import Twentythird.Map

/-!
# Reachability and the exchange of the two relations

`ReachR3 G H`: some sequence of changes from `G` ends at a state of `H`'s
result.  Derived here:
* **the twenty-second's criterion holds** (`reach3_criterion`): a result
  reaches another exactly when the other has a term or the first is the empty
  state — it is decided by the number of terms, which this seed's sameness
  keeps; so it does not depend on which state of the first result the
  changes start from (`reach3_of_same3`), and results with a term reach each
  other both ways (`reach3_mutual`);
* **the exchange of the two relations is still a symmetry**: it keeps this
  seed's sameness both ways (`same3_swap_iff`), the cost (`cost3_swap`) and
  reachability (`reach3_swap`).
-/

namespace Twentythird

open Twentysecond

/-- Some sequence of changes from `G` ends at a state of `H`'s result. -/
def ReachR3 (G H : St) : Prop := ∃ k H', Reach G H' k ∧ Same3 H' H

/-- **Reachability: a result reaches another exactly when the other has a term or the first is empty.** -/
theorem reach3_criterion {G H : St} (hG : G.WF) (hH : H.WF) : ReachR3 G H ↔ 0 < H.n ∨ G.n = 0 := by
  constructor
  · rintro ⟨k, H', r, s⟩
    by_cases h0 : G.n = 0
    · exact Or.inr h0
    · exact Or.inl (s.n ▸ r.n_pos hG (by omega))
  · intro h
    obtain ⟨k, H', r, s⟩ := (reach_criterion hG hH).2 h
    exact ⟨k, H', r, Same.same3 s⟩

/-- Whichever state of a result the changes start from, the results reached are the same. -/
theorem reach3_of_same3 {G G' H : St} (hG : G.WF) (hG' : G'.WF) (hH : H.WF) (s : Same3 G G') :
    ReachR3 G H ↔ ReachR3 G' H := by
  rw [reach3_criterion hG hH, reach3_criterion hG' hH, s.n]

theorem reach3_mutual {G H : St} (hG : G.WF) (hH : H.WF) (g : 0 < G.n) (h : 0 < H.n) :
    ReachR3 G H ∧ ReachR3 H G :=
  ⟨(reach3_criterion hG hH).2 (Or.inl h), (reach3_criterion hH hG).2 (Or.inl g)⟩

theorem Same3.swap {G H : St} (h : Same3 G H) : Same3 G.swap H.swap := by
  obtain ⟨hn, g, hg⟩ := h
  refine ⟨hn, fun x => - g x, fun x y hx hy => ?_⟩
  show excess G.swap x y = excess H.swap x y + (- g x - - g y)
  rw [excess_swap, excess_swap, hg x y hx hy]
  omega

/-- **The exchange keeps this seed's sameness, both ways.** -/
theorem same3_swap_iff {G H : St} : Same3 G H ↔ Same3 G.swap H.swap := by
  constructor
  · exact Same3.swap
  · intro h
    have := h.swap
    rwa [swap_swap, swap_swap] at this

theorem reach_swap {G H : St} {k : Nat} (h : Reach G H k) : Reach G.swap H.swap k := by
  induction h with
  | refl => exact Reach.refl _
  | step _ st ih => exact Reach.step ih st.swap

theorem empty_swap : empty.swap = empty := rfl

/-- **The exchange keeps the cost.** -/
theorem cost3_swap {G : St} {c : Nat} : Cost3 G c ↔ Cost3 G.swap c := by
  have key : ∀ {G : St}, Cost3 G c → Cost3 G.swap c := by
    intro G ⟨⟨H, s, r⟩, lo⟩
    refine ⟨⟨H.swap, s.swap, empty_swap ▸ reach_swap r⟩, fun K k sK rK => ?_⟩
    have := sK.swap
    rw [swap_swap] at this
    exact lo K.swap k this (empty_swap ▸ reach_swap rK)
  constructor
  · exact key
  · intro h
    have := key h
    rwa [swap_swap] at this

/-- **The exchange keeps reachability.** -/
theorem reach3_swap {G H : St} (hG : G.WF) (hH : H.WF) : ReachR3 G H ↔ ReachR3 G.swap H.swap := by
  rw [reach3_criterion hG hH, reach3_criterion (swap_wf hG) (swap_wf hH)]
  rfl

end Twentythird
