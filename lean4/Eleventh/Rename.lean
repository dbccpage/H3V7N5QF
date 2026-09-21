import Eleventh.Compare

/-!
# Exchange of the relations carries writings

Plan target 4.  The terms are unchanged by the exchange (`swap9_T`), so a
writing of the terms is the same writing, and determination of `q` on `s` is
determination of `!q` on `s.swap`.
-/

namespace Seed.Eleventh

open Seed Seed.Ninth Seed.Eighth NDSt

theorem determinesRel_swap (s : NDSt) (w : ℕ → ℕ) (q : Rel) :
    determinesRel s.swap w q ↔ determinesRel s w (!q) := by
  constructor
  · intro h L K x y x' y' hx hy hx' hy' hL hK hL' hK'
    have hxS : x ∈ s.swap.T := by simpa [NDSt.swap] using hx
    have hyS : y ∈ s.swap.T := by simpa [NDSt.swap] using hy
    have hxS' : x' ∈ s.swap.T := by simpa [NDSt.swap] using hx'
    have hyS' : y' ∈ s.swap.T := by simpa [NDSt.swap] using hy'
    have := h L K x y x' y' hxS hyS hxS' hyS' hL hK hL' hK'
    simpa [NDSt.swap] using this
  · intro h L K x y x' y' hx hy hx' hy' hL hK hL' hK'
    have hxS : x ∈ s.T := by simpa [NDSt.swap] using hx
    have hyS : y ∈ s.T := by simpa [NDSt.swap] using hy
    have hxS' : x' ∈ s.T := by simpa [NDSt.swap] using hx'
    have hyS' : y' ∈ s.T := by simpa [NDSt.swap] using hy'
    have := h L K x y x' y' hxS hyS hxS' hyS' hL hK hL' hK'
    simpa [NDSt.swap] using this

theorem determines_swap (s : NDSt) (w : ℕ → ℕ) :
    determines s.swap w ↔ determines s w := by
  constructor
  · intro h q
    have := (determinesRel_swap s w (!q)).1 (h (!q))
    simpa using this
  · intro h q
    exact (determinesRel_swap s w q).2 (h (!q))

theorem Step11.swap {s t : NDSt} (h : Step11 s t) : Step11 s.swap t.swap :=
  Step9.swap h

end Seed.Eleventh
