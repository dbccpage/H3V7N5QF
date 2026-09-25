/-!
# Problem 07: Two-Term Readings Formalization in Lean 4

Seed edit from Eighteenth seed:
"A reading names at most two terms and records the assertions between them.
Two results are the same if every such reading gives the same record."

This formalization establishes:
1. `LocalRecord`: The extraction of 0-, 1-, and 2-term sub-reading records.
2. `LocalEquiv`: The equivalence relation defined by agreement of local record sets.
3. Proof that `LocalEquiv` is reflexive, symmetric, and transitive.
4. Witness 1: `arb` and `bra` are distinct written states on two terms, yet locally equivalent.
5. Witness 2: Two non-isomorphic states on three terms (2 assertions vs 4 assertions)
   are locally equivalent.
6. Step non-congruence: Demonstrates that the one-step transition system does NOT descend
   to equivalence classes of `LocalEquiv`.
-/

/-- Induced assertion configuration between two ordered terms. -/
inductive EdgeConfig : Type
  | none : EdgeConfig
  | fwd  : EdgeConfig
  | bwd  : EdgeConfig
  | both : EdgeConfig
  deriving DecidableEq, Repr

/-- A local reading record of at most two terms:
- `rec0`: the 0-term reading (no terms named)
- `rec1`: a 1-term reading recording whether a self-loop is present
- `rec2`: a 2-term reading recording the induced assertions between two ordered terms
-/
inductive LocalRecord : Type
  | rec0 : LocalRecord
  | rec1 (loop : Bool) : LocalRecord
  | rec2 (cfg : EdgeConfig) : LocalRecord
  deriving DecidableEq, Repr

/-- A finite state with `n` terms (0 .. n-1) and a list of asserted pairs. -/
structure LState where
  n : Nat
  A : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- Membership test for directed assertions. -/
def hasEdge (s : LState) (u v : Nat) : Bool :=
  (u, v) ∈ s.A

/-- Extract the edge configuration between two distinct terms u and v. -/
def edgeBetween (s : LState) (u v : Nat) : EdgeConfig :=
  match hasEdge s u v, hasEdge s v u with
  | true, true   => EdgeConfig.both
  | true, false  => EdgeConfig.fwd
  | false, true  => EdgeConfig.bwd
  | false, false => EdgeConfig.none

/-- The complete list of local reading records for a state. -/
def allRecords (s : LState) : List LocalRecord :=
  let r0 := [LocalRecord.rec0]
  let r1 := (List.range s.n).map (fun u => LocalRecord.rec1 (hasEdge s u u))
  let r2 := (List.range s.n).flatMap (fun u =>
    (List.range s.n).filterMap (fun v =>
      if u ≠ v then some (LocalRecord.rec2 (edgeBetween s u v)) else none
    )
  )
  r0 ++ r1 ++ r2

/-- Two results are the same if every such reading gives the same record. -/
def LocalEquiv (s1 s2 : LState) : Prop :=
  ∀ r : LocalRecord, r ∈ allRecords s1 ↔ r ∈ allRecords s2

/-! ## Equivalence relation properties -/

theorem localEquiv_refl (s : LState) : LocalEquiv s s := by
  intro r
  exact Iff.rfl

theorem localEquiv_symm {s1 s2 : LState} (h : LocalEquiv s1 s2) : LocalEquiv s2 s1 := by
  intro r
  exact (h r).symm

theorem localEquiv_trans {s1 s2 s3 : LState} (h12 : LocalEquiv s1 s2) (h23 : LocalEquiv s2 s3) :
    LocalEquiv s1 s3 := by
  intro r
  exact (h12 r).trans (h23 r)

/-- Decision helper for local equivalence of concrete finite states. -/
theorem localEquiv_decide {s1 s2 : LState}
    (h : (∀ r ∈ allRecords s1, r ∈ allRecords s2) ∧ (∀ r ∈ allRecords s2, r ∈ allRecords s1)) :
    LocalEquiv s1 s2 := by
  intro r
  constructor
  · exact fun hr => h.1 r hr
  · exact fun hr => h.2 r hr

/-! ## Witness 1: Collapsing distinct written states at n = 2 -/

/-- `arb` asserted on two terms. -/
def s_arb : LState := ⟨2, [(0, 1)]⟩

/-- `bra` asserted on two terms. -/
def s_bra : LState := ⟨2, [(1, 0)]⟩

/-- In the eighteenth derivation, these are distinct results. -/
theorem s_arb_ne_s_bra : s_arb ≠ s_bra := by
  intro h
  injection h with h1 h2
  have : [(0, 1)] ≠ [(1, 0)] := by decide
  exact this h2

/-- Under local readings, every such reading gives the same record. -/
theorem arb_equiv_bra : LocalEquiv s_arb s_bra := by
  apply localEquiv_decide
  decide

/-! ## Witness 2: Collapsing non-isomorphic states at n = 3 -/

/-- State A: 3 terms, one 2-cycle (arb, bra) and one isolated vertex (2 assertions). -/
def s_A : LState := ⟨3, [(0, 1), (1, 0)]⟩

/-- State B: 3 terms, two 2-cycles (arb, bra, arc, cra) (4 assertions). -/
def s_B : LState := ⟨3, [(0, 1), (1, 0), (0, 2), (2, 0)]⟩

/-- They have different edge counts, so they are non-isomorphic under FREE rewriting. -/
theorem s_A_ne_s_B_size : s_A.A.length ≠ s_B.A.length := by decide

/-- Yet every local reading of at most two terms yields the same record set. -/
theorem s_A_equiv_s_B : LocalEquiv s_A s_B := by
  apply localEquiv_decide
  decide

/-! ## Step non-congruence -/

/-- One-step assertion removal transition. -/
def stepRemove (s : LState) (p : Nat × Nat) : LState :=
  ⟨s.n, s.A.erase p⟩

/-- One step from s_A removing (1, 0) leaves a single directed edge. -/
def s_A_next : LState := stepRemove s_A (1, 0)

/-- s_A_next has no bidirectional 2-cycle. -/
theorem s_A_next_has_no_both : LocalRecord.rec2 EdgeConfig.both ∉ allRecords s_A_next := by decide

/-- The four possible one-step removals from s_B. -/
def s_B_rem1 : LState := stepRemove s_B (0, 1)
def s_B_rem2 : LState := stepRemove s_B (1, 0)
def s_B_rem3 : LState := stepRemove s_B (0, 2)
def s_B_rem4 : LState := stepRemove s_B (2, 0)

/-- Every single removal from s_B leaves at least one bidirectional 2-cycle. -/
theorem s_B_rem1_has_both : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_B_rem1 := by decide
theorem s_B_rem2_has_both : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_B_rem2 := by decide
theorem s_B_rem3_has_both : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_B_rem3 := by decide
theorem s_B_rem4_has_both : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_B_rem4 := by decide

/-- Consequently, s_A_next is not locally equivalent to any single-removal outcome of s_B. -/
theorem s_A_next_not_equiv_s_B_rem1 : ¬ LocalEquiv s_A_next s_B_rem1 := by
  intro h
  have hb : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_A_next := (h _).2 s_B_rem1_has_both
  exact s_A_next_has_no_both hb

theorem s_A_next_not_equiv_s_B_rem2 : ¬ LocalEquiv s_A_next s_B_rem2 := by
  intro h
  have hb : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_A_next := (h _).2 s_B_rem2_has_both
  exact s_A_next_has_no_both hb

theorem s_A_next_not_equiv_s_B_rem3 : ¬ LocalEquiv s_A_next s_B_rem3 := by
  intro h
  have hb : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_A_next := (h _).2 s_B_rem3_has_both
  exact s_A_next_has_no_both hb

theorem s_A_next_not_equiv_s_B_rem4 : ¬ LocalEquiv s_A_next s_B_rem4 := by
  intro h
  have hb : LocalRecord.rec2 EdgeConfig.both ∈ allRecords s_A_next := (h _).2 s_B_rem4_has_both
  exact s_A_next_has_no_both hb
