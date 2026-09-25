/-
  Derivation for Problem 08: Record-order.

  Seed change from sixteenth:
  "Recorded leftovers are kept in the order they arise. Only the most recently
   recorded leftover may be admitted, adding the assertion `xry` or the assertion `xsy`;
   an unadmitted leftover is not an assertion."

  Formal targets:
  1. Ordered record definition (chronological sequence of leftover pairs).
  2. Count projection (forgetting order yields sixteenth's multiset count).
  3. Admissible last-element step (only the most recent leftover may be admitted).
  4. Minimal witness showing identical count projections but strictly different next-step admissions.
  5. Refutation of the falsifier ("all bounded results are classified by the old count alone").

  Integrity check: Zero sorry, zero admit, zero declared axioms.
-/

/-- An ordered pair representing the endpoints of a relation or leftover. -/
def Pair := Nat × Nat
deriving DecidableEq, Repr

/-- An ordered record of unadmitted leftovers kept in the order they arose (oldest to newest). -/
abbrev OrderedRecord := List Pair

/-- Count occurrences of a specific pair in an ordered record. -/
def countPair (p : Pair) : OrderedRecord → Nat
  | [] => 0
  | q :: rest => (if p = q then 1 else 0) + countPair p rest

/-- Projection to sixteenth's counted record: computes multiplicity of each pair. -/
def toCount (rec : OrderedRecord) (p : Pair) : Nat :=
  countPair p rec

/-- The most recently recorded leftover is the last element of the sequence. -/
def mostRecentLeftover : OrderedRecord → Option Pair
  | [] => none
  | xs => xs.getLast?

/--
  Admissibility condition:
  "Only the most recently recorded leftover may be admitted, adding the assertion `xry`
   or the assertion `xsy`; an unadmitted leftover is not an assertion."
-/
def isAdmissible (rec : OrderedRecord) (p : Pair) : Prop :=
  mostRecentLeftover rec = some p

/-- Admitting the most recent leftover pops it from the record. -/
def admitTop : OrderedRecord → OrderedRecord
  | [] => []
  | xs => xs.dropLast

/-- Recording a new leftover appends it to the end of the sequence. -/
def recordLeftover (rec : OrderedRecord) (p : Pair) : OrderedRecord :=
  rec ++ [p]

/-
  Witness instances:
  Two histories on 2 terms with identical leftover occurrences:
  witness1 has (0,0) recorded first, then (0,1).
  witness2 has (0,1) recorded first, then (0,0).
-/
def witness1 : OrderedRecord := [(0, 0), (0, 1)]
def witness2 : OrderedRecord := [(0, 1), (0, 0)]

/-- Both witness records have identical count projections for all pairs. -/
theorem witness_count_eq (p : Pair) : toCount witness1 p = toCount witness2 p := by
  dsimp [toCount, countPair, witness1, witness2]
  split <;> split <;> rfl

/-- In witness1, (0, 1) is admissible because it is the most recently recorded leftover. -/
theorem witness1_admissible : isAdmissible witness1 (0, 1) := by
  dsimp [isAdmissible, mostRecentLeftover, witness1]
  rfl

/-- In witness1, (0, 0) is NOT admissible because it is not the most recent leftover. -/
theorem witness1_not_admissible_other : ¬ isAdmissible witness1 (0, 0) := by
  dsimp [isAdmissible, mostRecentLeftover, witness1]
  intro h
  cases h

/-- In witness2, (0, 0) is admissible because it is the most recently recorded leftover. -/
theorem witness2_admissible : isAdmissible witness2 (0, 0) := by
  dsimp [isAdmissible, mostRecentLeftover, witness2]
  rfl

/-- In witness2, (0, 1) is NOT admissible because it is not the most recent leftover. -/
theorem witness2_not_admissible_other : ¬ isAdmissible witness2 (0, 1) := by
  dsimp [isAdmissible, mostRecentLeftover, witness2]
  intro h
  cases h

/--
  The admission sets of witness1 and witness2 are not equivalent.
  Thus, order-sensitive feedback restricts and alters the next admissible steps.
-/
theorem witness_different_admissions :
    ¬ (∀ p : Pair, isAdmissible witness1 p ↔ isAdmissible witness2 p) := by
  intro h
  have h_iff := h (0, 1)
  have h_w1 := witness1_admissible
  have h_w2_adm := h_iff.mp h_w1
  exact witness2_not_admissible_other h_w2_adm

/--
  Main Resolution Theorem:
  There exist two reachable records that have identical sixteenth count projections,
  yet have non-isomorphic next admissible transitions.
  This refutes the falsifier ("all bounded results are classified by the old count alone")
  and confirms the hypothesis ("order-sensitive feedback changes admission paths").
-/
theorem falsifier_refuted :
    ∃ (r1 r2 : OrderedRecord),
      (∀ p : Pair, toCount r1 p = toCount r2 p) ∧
      ¬ (∀ p : Pair, isAdmissible r1 p ↔ isAdmissible r2 p) := by
  exists witness1
  exists witness2
  exact ⟨witness_count_eq, witness_different_admissions⟩

#print axioms witness_count_eq
#print axioms witness1_admissible
#print axioms witness1_not_admissible_other
#print axioms witness2_admissible
#print axioms witness2_not_admissible_other
#print axioms witness_different_admissions
#print axioms falsifier_refuted
