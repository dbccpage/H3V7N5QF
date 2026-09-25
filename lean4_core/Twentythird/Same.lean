import Twentythird.Raise

/-!
# The seed's sameness at a fixed writing of the terms

"Two results that differ only in how their terms are written, only by an
`xry` and an `xsy` asserted together, or only by raising terms, are the same
result."  Here the terms keep their writing (rewriting is `Rename.lean`).

`Gen3` is the sameness these clauses generate at a fixed writing (reading
C-H1 of the paper): the twenty-second's generated sameness `Gen` (a rearranged
list; one more pair asserted together), or one term raised, closed under
symmetry and transitivity.

`Same3 G H`: equally many terms, and excesses differing by `g x − g y` at
every pair of terms, for some whole number `g x` per term.  Derived:
* `gen3_iff_same3`: for well-formed states the generated sameness *is*
  `Same3` — raising `x` moves the excess by `[u = x] − [v = x]`; conversely
  a difference `g x − g y` is reached by raising every term `x` some number of
  times (`g` moved up to be at least zero), then taking out pairs asserted
  together (the twenty-second's `gen_iff_same`);
* `Same3` is an equivalence, is coarser than the twenty-second's `Same`, and
  keeps the terms.
-/

namespace Twentythird

open Twentysecond

/-- The sameness the seed's clauses generate, at a fixed writing of the terms. -/
inductive Gen3 : St → St → Prop
  | gen {G H : St} : Gen G H → Gen3 G H
  | raise (G : St) (x : Nat) (hx : x < G.n) : Gen3 G (raise G x)
  | symm {G H : St} : Gen3 G H → Gen3 H G
  | trans {G H K : St} : Gen3 G H → Gen3 H K → Gen3 G K

/-- The seed's sameness at a fixed writing: equally many terms, excesses differing by `g x − g y`. -/
def Same3 (G H : St) : Prop :=
  G.n = H.n ∧ ∃ g : Nat → Int, ∀ x y, x < G.n → y < G.n → excess G x y = excess H x y + (g x - g y)

theorem Same3.refl (G : St) : Same3 G G :=
  ⟨rfl, fun _ => 0, fun x y _ _ => by show excess G x y = excess G x y + (0 - 0); omega⟩

theorem Same3.symm {G H : St} (h : Same3 G H) : Same3 H G := by
  obtain ⟨hn, g, hg⟩ := h
  refine ⟨hn.symm, fun x => - g x, fun x y hx hy => ?_⟩
  show excess H x y = excess G x y + (- g x - - g y)
  have := hg x y (hn ▸ hx) (hn ▸ hy)
  omega

theorem Same3.trans {G H K : St} (h1 : Same3 G H) (h2 : Same3 H K) : Same3 G K := by
  obtain ⟨hn1, g1, e1⟩ := h1
  obtain ⟨hn2, g2, e2⟩ := h2
  refine ⟨hn1.trans hn2, fun x => g1 x + g2 x, fun x y hx hy => ?_⟩
  show excess G x y = excess K x y + ((g1 x + g2 x) - (g1 y + g2 y))
  have a := e1 x y hx hy
  have b := e2 x y (hn1 ▸ hx) (hn1 ▸ hy)
  omega

theorem Same3.n {G H : St} (h : Same3 G H) : G.n = H.n := h.1

/-- The twenty-second's sameness is finer: its results stay results, merged. -/
theorem Same.same3 {G H : St} (h : Same G H) : Same3 G H := by
  obtain ⟨hn, he⟩ := same_iff_excess.1 h
  exact ⟨hn, fun _ => 0, fun x y _ _ => by
    show excess G x y = excess H x y + (0 - 0)
    rw [he x y]
    omega⟩

theorem same3_raise (G : St) (x : Nat) : Same3 G (raise G x) :=
  ⟨rfl, fun y => - (if y = x then 1 else 0), fun u v hu hv => by
    show excess G u v = excess (raise G x) u v + (- (if u = x then 1 else 0) - - (if v = x then 1 else 0))
    rw [excess_raise G x u v hu hv]
    omega⟩

theorem Gen3.same3 {G H : St} (h : Gen3 G H) : Same3 G H := by
  induction h with
  | gen g => exact Same.same3 g.same
  | raise G x _ => exact same3_raise G x
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem gen3_raiseN (G : St) (x : Nat) (hx : x < G.n) : ∀ m, Gen3 G (raiseN G x m)
  | 0 => Gen3.gen (Gen.perm rfl (List.Perm.refl _))
  | m + 1 => Gen3.trans (gen3_raiseN G x hx m) (Gen3.raise _ x (by rw [raiseN_n]; exact hx))

theorem gen3_raiseTo (G : St) (f : Nat → Nat) : ∀ k, k ≤ G.n → Gen3 G (raiseTo G f k)
  | 0, _ => Gen3.gen (Gen.perm rfl (List.Perm.refl _))
  | k + 1, hk =>
    Gen3.trans (gen3_raiseTo G f k (by omega)) (gen3_raiseN _ k (by rw [raiseTo_n]; omega) (f k))

/-- A number at most `g x` for every `x < k`. -/
def lowBound (g : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => min (lowBound g k) (g k)

theorem lowBound_le (g : Nat → Int) : ∀ k x, x < k → lowBound g k ≤ g x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, x, h => by
    simp only [lowBound]
    by_cases e : x = k
    · subst e
      exact Int.min_le_right _ _
    · exact Int.le_trans (Int.min_le_left _ _) (lowBound_le g k x (by omega))

/-- **The sameness the seed's three clauses generate is `Same3`** (well-formed states, fixed writing). -/
theorem gen3_iff_same3 {G H : St} (hG : G.WF) (hH : H.WF) : Gen3 G H ↔ Same3 G H := by
  constructor
  · exact Gen3.same3
  · rintro ⟨hn, g, hg⟩
    let f : Nat → Nat := fun x => (g x - lowBound g H.n).toNat
    have hf : ∀ x, x < H.n → (f x : Int) = g x - lowBound g H.n := by
      intro x hx
      have := lowBound_le g H.n x hx
      simp only [f]
      omega
    have hw := raiseTo_wf f hH H.n (Nat.le_refl _)
    have s : Same G (raiseTo H f H.n) := by
      refine same_iff_excess.2 ⟨hn.trans (raiseTo_n H f H.n).symm, fun u v => ?_⟩
      by_cases hu : u < G.n
      · by_cases hv : v < G.n
        · rw [excess_raiseTo_all H f u v (hn ▸ hu) (hn ▸ hv), hf u (hn ▸ hu), hf v (hn ▸ hv), hg u v hu hv]
          omega
        · rw [excess_out hG (Or.inr (by omega)), excess_out hw (Or.inr (by rw [raiseTo_n]; omega))]
      · rw [excess_out hG (Or.inl (by omega)), excess_out hw (Or.inl (by rw [raiseTo_n]; omega))]
    exact Gen3.trans (Gen3.gen ((gen_iff_same hG hw).2 s)) (Gen3.symm (gen3_raiseTo H f H.n (Nat.le_refl _)))

/-- Two states asserting nothing on equally many terms, one raised at a term: the same result. -/
theorem same3_of_excess {G H : St} (hn : G.n = H.n) (g : Nat → Int)
    (h : ∀ x y, x < G.n → y < G.n → excess G x y = excess H x y + (g x - g y)) : Same3 G H := ⟨hn, g, h⟩

end Twentythird
