import Fifteenth.Compare

/-!
# Exchange of the relations keeps the admission record

Plan target 4.  Admission names no relation, so exchanging the relations
keeps the record.  A change of the four kinds still leaves not-admitted.
-/

namespace Seed.Fifteenth

open Seed Seed.Ninth Seed.Eighth NDSt

theorem admission_swap : reaching = reaching := rfl

theorem admission_swap_admitted : admitted = admitted := rfl

theorem Step15.swap {s t : NDSt} (h : Step15 s t) : Step15 s.swap t.swap :=
  Step9.swap h

end Seed.Fifteenth
