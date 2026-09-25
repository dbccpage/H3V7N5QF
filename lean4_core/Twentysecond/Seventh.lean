import Twentysecond.Record

/-!
# The seventh's states map one to one into this seed's results

The seventh seed (`prompt/seventh/seed_prompt.md`, `paper/seventh/`, cited
through the ninth) has one relation, nothing given, and the four kinds of
change.  Its state is re-written here as the ninth's is: `n` terms and a list
of pairs, the multiplicity of `xry` being how often `(x, y)` occurs; two lists
that are rearrangements of each other are one state (`SameState7`).

* `ofR`: a seventh state read as a state of this seed asserting nothing with
  `s` (the ninth's `NSt.ofR`).  Every seventh change is carried to a change of
  the same kind (`Step7.embed`, `Reach7.embed`).
* **One to one**: two seventh states give the same result here exactly when
  they are the same seventh state (`ofR_same_iff`) — at a fixed writing; in
  every writing, `Rename.lean`.  The ninth's states do not map one to one
  (`ninth_not_one_to_one`), and no map carrying every ninth addition to the
  same addition here can keep them apart (`carried_additions_merge`).
* The map back `readBack` reads a result's plain part: its `r` part if it
  asserts nothing with `s`, "none" otherwise.  It returns the original on
  every mapped state (`readBack_ofR`); it answers "none" on the one-term
  result asserting `asa` once (`readBack_asa`); every result it answers
  "none" on costs at least two changes (`readBack_none_phi`), and the only one
  costing two is that one (`readBack_none_smallest`); it is a function of the
  result (`readBack_same`).
-/

namespace Twentysecond

/-- A state of the seventh seed: `n` terms and a list of pairs `(x, y)`, one relation. -/
structure St7 where
  n : Nat
  P : List (Nat × Nat)

namespace St7

def WF (M : St7) : Prop := ∀ p ∈ M.P, p.1 < M.n ∧ p.2 < M.n

def addTerm (M : St7) : St7 := ⟨M.n + 1, M.P⟩

def add (M : St7) (p : Nat × Nat) : St7 := ⟨M.n, p :: M.P⟩

def remove (M : St7) (p : Nat × Nat) : St7 := ⟨M.n, del p M.P⟩

def identify (M : St7) (u v : Nat) : St7 :=
  ⟨M.n - 1, M.P.map (fun p => (glue M.n u v p.1, glue M.n u v p.2))⟩

end St7

/-- One change of the seventh seed (the four kinds, one relation). -/
inductive Step7 : St7 → St7 → Prop
  | addTerm (M : St7) : Step7 M M.addTerm
  | add (M : St7) (p : Nat × Nat) (hx : p.1 < M.n) (hy : p.2 < M.n) : Step7 M (M.add p)
  | remove (M : St7) (p : Nat × Nat) (h : p ∈ M.P) : Step7 M (M.remove p)
  | identify (M : St7) (u v : Nat) (hu : u < M.n) (hv : v < M.n) (huv : u ≠ v) : Step7 M (M.identify u v)

inductive Reach7 : St7 → St7 → Nat → Prop
  | refl (M : St7) : Reach7 M M 0
  | step {M M' M'' : St7} {k : Nat} : Reach7 M M' k → Step7 M' M'' → Reach7 M M'' (k + 1)

/-- The same seventh state: equally many terms, the same multiplicities. -/
def SameState7 (M M' : St7) : Prop := M.n = M'.n ∧ M.P.Perm M'.P

/-- A pair as an `r` atom. -/
def rAtom (p : Nat × Nat) : Atom := ⟨.r, p.1, p.2⟩

theorem rAtom_inj : ∀ p p' : Nat × Nat, rAtom p = rAtom p' → p = p' := by
  intro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [rAtom, Atom.mk.injEq] at h
  rw [h.2.1, h.2.2]

/-- A seventh state read as a state of this seed asserting nothing with `s`. -/
def ofR (M : St7) : St := ⟨M.n, M.P.map rAtom⟩

theorem ofR_wf {M : St7} (hw : M.WF) : (ofR M).WF := by
  intro a ha
  obtain ⟨p, hp, e⟩ := List.mem_map.1 ha
  subst e
  exact hw p hp

/-- **Every change of the seventh seed is carried to a change of the same kind here.** -/
theorem Step7.embed {M M' : St7} (h : Step7 M M') : Step (ofR M) (ofR M') := by
  cases h with
  | addTerm => exact Step.addTerm (ofR M)
  | add p hx hy => exact Step.add (ofR M) (rAtom p) hx hy
  | remove p hp =>
    have e : ofR (M.remove p) = (ofR M).remove (rAtom p) := by
      simp only [ofR, St7.remove, St.remove, map_del_of_inj rAtom_inj]
    rw [e]
    exact Step.remove (ofR M) (rAtom p) (List.mem_map_of_mem hp)
  | identify u v hu hv huv =>
    have e : ofR (M.identify u v) = (ofR M).identify u v := by
      simp only [ofR, St7.identify, St.identify, List.map_map]
      rfl
    rw [e]
    exact Step.identify (ofR M) u v hu hv huv

theorem Reach7.embed {M M' : St7} {k : Nat} (h : Reach7 M M' k) : Reach (ofR M) (ofR M') k := by
  induction h with
  | refl => exact Reach.refl _
  | step _ st ih => exact Reach.step ih st.embed

/-- An embedded seventh state is its own plain part: nothing is asserted with `s`. -/
theorem plain_ofR (M : St7) : plain (ofR M).A = (ofR M).A := by
  apply plain_eq_self
  intro a ha hp
  obtain ⟨p, _, e⟩ := List.mem_map.1 ha
  obtain ⟨p', _, e'⟩ := List.mem_map.1 hp
  subst e
  have := congrArg Atom.q e'
  simp [rAtom, Atom.partner, Rel.other] at this

/-- The seventh's cost (terms plus assertions) is this seed's cost of the embedded result. -/
theorem phi_ofR (M : St7) : phi (ofR M) = M.n + M.P.length := by
  unfold phi
  rw [plain_ofR]
  simp only [ofR, List.length_map]

/-- **One to one**: two seventh states are the same result here exactly when they are the same
seventh state. -/
theorem ofR_same_iff {M M' : St7} : Same (ofR M) (ofR M') ↔ SameState7 M M' := by
  unfold Same SameState7
  rw [plain_ofR, plain_ofR]
  constructor
  · rintro ⟨hn, hp⟩
    exact ⟨hn, perm_of_perm_map_of_inj rAtom_inj hp⟩
  · rintro ⟨hn, hp⟩
    exact ⟨hn, hp.map rAtom⟩

/-! ## The map back -/

/-- The pairs of a list of `r` atoms; "none" as soon as an atom is written with `s`. -/
def rParts : List Atom → Option (List (Nat × Nat))
  | [] => some []
  | a :: l =>
    match a.q, rParts l with
    | .r, some P => some ((a.x, a.y) :: P)
    | _, _ => none

theorem rParts_map (P : List (Nat × Nat)) : rParts (P.map rAtom) = some P := by
  induction P with
  | nil => rfl
  | cons p t ih => simp only [List.map_cons, rParts, rAtom, ih]

theorem rParts_some {l : List Atom} {P : List (Nat × Nat)} (h : rParts l = some P) : l = P.map rAtom := by
  induction l generalizing P with
  | nil =>
    simp only [rParts, Option.some.injEq] at h
    subst h
    rfl
  | cons a t ih =>
    obtain ⟨q, x, y⟩ := a
    cases q with
    | s => simp [rParts] at h
    | r =>
      cases ht : rParts t with
      | none => simp [rParts, ht] at h
      | some P' =>
        simp only [rParts, ht, Option.some.injEq] at h
        subst h
        rw [ih ht]
        rfl

theorem rParts_none {l : List Atom} (h : rParts l = none) : ∃ a ∈ l, a.q = .s := by
  induction l with
  | nil => simp [rParts] at h
  | cons a t ih =>
    obtain ⟨q, x, y⟩ := a
    cases q with
    | s => exact ⟨_, List.mem_cons_self, rfl⟩
    | r =>
      cases ht : rParts t with
      | none =>
        obtain ⟨b, hb, e⟩ := ih ht
        exact ⟨b, List.mem_cons_of_mem _ hb, e⟩
      | some P' => simp [rParts, ht] at h

theorem rParts_some_of_all_r {l : List Atom} (h : ∀ a ∈ l, a.q = .r) : ∃ P, rParts l = some P := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a t ih =>
    obtain ⟨P, hP⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    obtain ⟨q, x, y⟩ := a
    have : q = .r := h _ List.mem_cons_self
    subst this
    exact ⟨(x, y) :: P, by simp [rParts, hP]⟩

/-- The map back: a result's plain part as a seventh state, if it asserts nothing with `s`. -/
def readBack (G : St) : Option St7 :=
  match rParts (plain G.A) with
  | some P => some ⟨G.n, P⟩
  | none => none

/-- **The map back returns the original on every mapped state.** -/
theorem readBack_ofR (M : St7) : readBack (ofR M) = some M := by
  unfold readBack
  rw [plain_ofR]
  simp only [ofR, rParts_map]

/-- The one-term result asserting `asa` once. -/
def asa : St := ⟨1, [⟨.s, 0, 0⟩]⟩

theorem asa_wf : asa.WF := by
  intro a ha
  rcases List.mem_cons.1 ha with e | h
  · subst e; exact ⟨by decide, by decide⟩
  · exact absurd h List.not_mem_nil

/-- **The map back answers "none"** on the one-term result asserting `asa` once. -/
theorem readBack_asa : readBack asa = none := rfl

/-- Every result the map back answers "none" on costs at least two changes. -/
theorem readBack_none_phi {G : St} (hw : G.WF) (h : readBack G = none) : 2 ≤ phi G := by
  have hr : rParts (plain G.A) = none := by
    unfold readBack at h
    cases e : rParts (plain G.A) with
    | none => rfl
    | some P => rw [e] at h; exact absurd h (by simp)
  obtain ⟨a, ha, _⟩ := rParts_none hr
  have hx := (hw a (mem_of_mem_plain ha)).1
  have hl : 0 < (plain G.A).length := length_pos_of_mem' ha
  simp only [phi]
  omega

/-- **The smallest result the map back answers "none" on**: the only one costing two changes is the
one-term result asserting `asa` once. -/
theorem readBack_none_smallest {G : St} (hw : G.WF) (h : readBack G = none) (h2 : phi G = 2) :
    Same G asa := by
  have hr : rParts (plain G.A) = none := by
    unfold readBack at h
    cases e : rParts (plain G.A) with
    | none => rfl
    | some P => rw [e] at h; exact absurd h (by simp)
  obtain ⟨a, ha, hs⟩ := rParts_none hr
  have hx := (hw a (mem_of_mem_plain ha)).1
  have hy := (hw a (mem_of_mem_plain ha)).2
  have hl : 0 < (plain G.A).length := length_pos_of_mem' ha
  simp only [phi] at h2
  have hn : G.n = 1 := by omega
  have h1 : (plain G.A).length = 1 := by omega
  cases hp : plain G.A with
  | nil => rw [hp] at ha; exact absurd ha List.not_mem_nil
  | cons b t =>
    rw [hp] at h1 ha
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons c t' =>
        rw [List.length_cons, List.length_cons] at h1
        omega
    subst ht
    rcases List.mem_cons.1 ha with e | e
    · subst e
      obtain ⟨q, x, y⟩ := a
      simp only at hs hx hy
      subst hs
      have ex : x = 0 := by omega
      have ey : y = 0 := by omega
      subst ex
      subst ey
      exact ⟨hn, by rw [hp]; rfl⟩
    · exact absurd e List.not_mem_nil

/-- The map back is a function of the result: same results give the same seventh state, or both
"none". -/
theorem readBack_same {G H : St} (h : Same G H) :
    (readBack G = none ↔ readBack H = none) ∧
      ∀ M M', readBack G = some M → readBack H = some M' → SameState7 M M' := by
  have key : ∀ {G H : St}, Same G H → readBack G = none → readBack H = none := by
    intro G H h hG
    have hr : rParts (plain G.A) = none := by
      unfold readBack at hG
      cases e : rParts (plain G.A) with
      | none => rfl
      | some P => rw [e] at hG; exact absurd hG (by simp)
    obtain ⟨a, ha, hs⟩ := rParts_none hr
    have ha' : a ∈ plain H.A := h.2.mem_iff.1 ha
    unfold readBack
    cases e : rParts (plain H.A) with
    | none => rfl
    | some P =>
      have := rParts_some e
      rw [this] at ha'
      obtain ⟨p, _, e'⟩ := List.mem_map.1 ha'
      subst e'
      simp [rAtom] at hs
  refine ⟨⟨key h, key h.symm⟩, ?_⟩
  intro M M' hM hM'
  unfold readBack at hM hM'
  cases e : rParts (plain G.A) with
  | none => rw [e] at hM; exact absurd hM (by simp)
  | some P =>
    cases e' : rParts (plain H.A) with
    | none => rw [e'] at hM'; exact absurd hM' (by simp)
    | some P' =>
      rw [e] at hM
      rw [e'] at hM'
      simp only [Option.some.injEq] at hM hM'
      subst hM hM'
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [rParts_some e, rParts_some e'] at h2
      exact perm_of_perm_map_of_inj rAtom_inj h2

/-- **The results the map back answers are exactly the embedded seventh states**: when it answers
`M`, the result is the one of `ofR M`. -/
theorem same_ofR_of_readBack {G : St} {M : St7} (h : readBack G = some M) : Same G (ofR M) := by
  unfold readBack at h
  cases e : rParts (plain G.A) with
  | none => rw [e] at h; exact absurd h (by simp)
  | some P =>
    rw [e] at h
    simp only [Option.some.injEq] at h
    subst h
    refine (same_plainSt G).trans ⟨rfl, ?_⟩
    have hp : plain G.A = P.map rAtom := rParts_some e
    have hq : plain (P.map rAtom) = P.map rAtom := plain_ofR ⟨G.n, P⟩
    have h2 : plain (plain G.A) = plain (P.map rAtom) := by rw [plain_plain, hq, hp]
    exact List.Perm.of_eq h2

/-! ## The ninth's states do not map one to one -/

/-- The one-term state asserting nothing. -/
def oneTerm : St := ⟨1, []⟩

/-- The one-term state asserting `ara` and `asa` once each. -/
def oneTermBoth : St := ⟨1, [⟨.r, 0, 0⟩, ⟨.s, 0, 0⟩]⟩

/-- **The ninth's states do not map one to one**: two different ninth states, one result here. -/
theorem ninth_not_one_to_one : ¬ SameState9 oneTerm oneTermBoth ∧ Same oneTerm oneTermBoth := by
  refine ⟨fun h => ?_, ⟨rfl, ?_⟩⟩
  · have := h.2.length_eq
    simp [oneTerm, oneTermBoth] at this
  · have e : plain oneTermBoth.A = [] := rfl
    rw [e]
    exact List.Perm.refl _

/-- **No map carrying every ninth addition to the same addition here keeps the ninth's states
apart**: if `f` sends the empty state to the empty result and commutes with both additions up to
this seed's sameness, it sends `a` and `a; ara asa` to one result. -/
theorem carried_additions_merge (f : St → St) (h0 : Same (f empty) empty)
    (hT : ∀ G, Same (f G.addTerm) (f G).addTerm) (hA : ∀ G a, Same (f (G.add a)) ((f G).add a)) :
    Same (f oneTerm) (f oneTermBoth) := by
  have h1 : Same (f oneTerm) oneTerm := (hT empty).trans h0.addTerm
  have e : oneTermBoth = (oneTerm.add ⟨.s, 0, 0⟩).add ⟨.r, 0, 0⟩ := rfl
  have h2 : Same (f oneTermBoth) oneTermBoth := by
    rw [e]
    exact (hA _ _).trans (((hA _ _).trans (h1.add _)).add _)
  exact h1.trans (ninth_not_one_to_one.2.trans h2.symm)

end Twentysecond
