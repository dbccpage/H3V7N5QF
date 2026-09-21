import Twelfth.Compare

/-!
# Exchange of the relations carries identification records

Plan target 4.  The terms are unchanged by the exchange (`swap9_T`), so the
2×2 block of one relation on `s` is the 2×2 block of the other relation on
`s.swap`.
-/

namespace Seed.Twelfth

open Seed Seed.Ninth Seed.Eighth NDSt

theorem recordRel_swap (s : NDSt) (q : Rel) (u v : ℕ) :
    recordRel s.swap q u v = recordRel s (!q) u v := by
  unfold recordRel NDSt.swap
  rfl

theorem recordOf_swap (s : NDSt) (u v : ℕ) :
    recordOf s.swap u v = ⟨(recordOf s u v).s, (recordOf s u v).r⟩ := by
  simp [recordOf, recordRel_swap]

theorem Step12.swap {s t : NDSt} (h : Step12 s t) : Step12 s.swap t.swap :=
  Step9.swap h

end Seed.Twelfth
