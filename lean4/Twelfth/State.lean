import Eleventh.Rename

/-!
# Identification records, and the unchosen recorded reading

`prompt/twelfth/seed_prompt.md` is the ninth seed with one passage added:
identifying two terms records, for each relation, which assertions of those
two terms become one assertion, and the record is kept with the result.

The state of the twelfth seed under the chosen reading C-M1 is the ninth's
`NDSt`.  The record of an identification is computed from the start and the
two terms (`recordRel`).  The unchosen reading C-M2 tags a ninth state with
whether an identification record is attached (`Recorded`).
-/

namespace Seed.Twelfth

open Seed Seed.Ninth Seed.Eighth Seed.Eleventh NDSt

/-- Tags for the 2×2 block of assertions among the two identified terms. -/
inductive LoopTag
  | xx
  | xy
  | yx
  | yy
  deriving DecidableEq

/-- The record of identifying `u` and `v` in one relation: which of the four
pairs among those two terms were asserted (they all become the merged loop). -/
def recordRel (s : NDSt) (q : Rel) (u v : ℕ) : Finset LoopTag :=
  (if s.M q (u, u) = 0 then (∅ : Finset LoopTag) else {LoopTag.xx}) ∪
  (if s.M q (u, v) = 0 then (∅ : Finset LoopTag) else {LoopTag.xy}) ∪
  (if s.M q (v, u) = 0 then (∅ : Finset LoopTag) else {LoopTag.yx}) ∪
  (if s.M q (v, v) = 0 then (∅ : Finset LoopTag) else {LoopTag.yy})

/-- The pair of per-relation records of one identification. -/
structure IdentRecord where
  r : Finset LoopTag
  s : Finset LoopTag

def recordOf (s : NDSt) (u v : ℕ) : IdentRecord :=
  ⟨recordRel s false u v, recordRel s true u v⟩

/-- Unchosen reading C-M2: a ninth state together with whether an identification
record is attached. -/
structure Recorded where
  state : NDSt
  tagged : Bool

namespace Recorded

/-- The ninth's size: a record is not an assertion and is not counted. -/
def size (t : Recorded) : ℕ := t.state.size

/-- The empty beginning, with no identification record. -/
def start : Recorded := ⟨empty9, false⟩

/-- The one-term state, never identified. -/
def onePlain : Recorded := ⟨oneTerm9, false⟩

/-- The one-term state, tagged as reached by identifying two isolated terms. -/
def oneIdent : Recorded := ⟨oneTerm9, true⟩

end Recorded

/-- The record of one relation is determined by that relation's multiplicities. -/
theorem recordRel_of_M {s t : NDSt} {q : Rel} (h : s.M q = t.M q) (u v : ℕ) :
    recordRel s q u v = recordRel t q u v := by
  simp [recordRel, h]

theorem record_determined_by_rel (s : NDSt) (u v : ℕ) :
    recordRel s false u v = recordRel ⟨s.T, fun q p => if q = false then s.M false p else 0⟩ false u v := by
  simp [recordRel]

theorem twoBetween_record_r :
    LoopTag.xy ∈ recordRel twoBetween false 0 1 := by
  simp [recordRel, twoBetween]

theorem twoBetween_record_s :
    recordRel twoBetween true 0 1 = ∅ := by
  simp [recordRel, twoBetween]

theorem r_record_not_s :
    LoopTag.xy ∈ recordRel twoBetween false 0 1 ∧
      recordRel twoBetween true 0 1 = ∅ :=
  ⟨twoBetween_record_r, twoBetween_record_s⟩

theorem record_not_assertion (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  ⟨rfl, rfl⟩

end Seed.Twelfth
