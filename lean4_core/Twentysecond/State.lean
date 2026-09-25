import Twentysecond.Basic

/-!
# States and changes (the ninth's, re-written without the outside library)

A state has `n` terms, written `0 … n − 1`, and a list of atoms: the
multiplicity of `xqy` is the number of times the atom `⟨q, x, y⟩` occurs.
This is the ninth derivation's state (`paper/ninth/`, `lean4/Ninth/State.lean`:
a finite set of terms and a multiplicity function for each relation) written
with its terms numbered from `0` — a rewriting, which neither seed
distinguishes — and its multiplicity functions as counts.  Two lists that are
rearrangements of each other are the same ninth state (`SameState9`).

The four kinds of change (given by the seed, the ninth's word for word):
* adding a term: the term `n`;
* adding an assertion between two terms that are there (`xrx`, `xsx` allowed);
* removing an assertion that is asserted;
* identifying two different terms `u`, `v`: both become one term in every
  assertion of both relations, the multiplicities of the pairs that become one
  adding up (the list keeps every atom).  So that the terms stay
  `0 … n − 2`, `v` goes onto `u` and then the last term `n − 1` is written in
  the freed place `v` (`glue`): a rewriting of the ninth's outcome.

`Reach G H k`: `H` is reached from `G` by `k` changes.  `AddStep`: the two
additions only.
-/

namespace Twentysecond

/-- A state: `n` terms, and the assertions as a list of atoms. -/
structure St where
  n : Nat
  A : List Atom

namespace St

/-- Every assertion is between terms that are there. -/
def WF (G : St) : Prop := ∀ a ∈ G.A, a.x < G.n ∧ a.y < G.n

/-- The ninth's size: terms plus assertions of both relations, counted with multiplicity. -/
def size (G : St) : Nat := G.n + G.A.length

/-- Adding a term. -/
def addTerm (G : St) : St := ⟨G.n + 1, G.A⟩

/-- Adding an assertion: its multiplicity rises by one. -/
def add (G : St) (a : Atom) : St := ⟨G.n, a :: G.A⟩

/-- Removing an assertion: its multiplicity falls by one. -/
def remove (G : St) (a : Atom) : St := ⟨G.n, del a G.A⟩

end St

/-- What is given: no terms, nothing asserted. -/
def empty : St := ⟨0, []⟩

/-- Where term `w` goes when `u` and `v` are identified in a state with `n` terms. -/
def glue (n u v w : Nat) : Nat :=
  if (if w = v then u else w) = n - 1 then v else (if w = v then u else w)

/-- An atom with its terms moved by `f`; the relation is kept. -/
def Atom.mapT (f : Nat → Nat) (a : Atom) : Atom := ⟨a.q, f a.x, f a.y⟩

theorem Atom.mapT_partner (f : Nat → Nat) (a : Atom) : (a.mapT f).partner = a.partner.mapT f := rfl

/-- Identifying `u` and `v` in every assertion of both relations. -/
def St.identify (G : St) (u v : Nat) : St := ⟨G.n - 1, G.A.map (Atom.mapT (glue G.n u v))⟩

theorem glue_lt {n u v w : Nat} (hu : u < n) (hv : v < n) (huv : u ≠ v) (hw : w < n) :
    glue n u v w < n - 1 := by
  unfold glue
  by_cases h1 : w = v
  · simp only [h1, if_true]
    by_cases h2 : u = n - 1
    · simp only [h2, if_true]
      omega
    · simp only [h2, if_false]
      omega
  · simp only [h1, if_false]
    by_cases h2 : w = n - 1
    · simp only [h2, if_true]
      omega
    · simp only [h2, if_false]
      omega

/-- One change of the seed. -/
inductive Step : St → St → Prop
  | addTerm (G : St) : Step G G.addTerm
  | add (G : St) (a : Atom) (hx : a.x < G.n) (hy : a.y < G.n) : Step G (G.add a)
  | remove (G : St) (a : Atom) (h : a ∈ G.A) : Step G (G.remove a)
  | identify (G : St) (u v : Nat) (hu : u < G.n) (hv : v < G.n) (huv : u ≠ v) : Step G (G.identify u v)

/-- `Reach G H k`: `H` is reached from `G` by `k` changes. -/
inductive Reach : St → St → Nat → Prop
  | refl (G : St) : Reach G G 0
  | step {G H K : St} {k : Nat} : Reach G H k → Step H K → Reach G K (k + 1)

/-- The two additions. -/
inductive AddStep : St → St → Prop
  | addTerm (G : St) : AddStep G G.addTerm
  | add (G : St) (a : Atom) (hx : a.x < G.n) (hy : a.y < G.n) : AddStep G (G.add a)

/-- `AddReach G H k`: `H` is reached from `G` by `k` additions. -/
inductive AddReach : St → St → Nat → Prop
  | refl (G : St) : AddReach G G 0
  | step {G H K : St} {k : Nat} : AddReach G H k → AddStep H K → AddReach G K (k + 1)

theorem AddStep.step {G H : St} (h : AddStep G H) : Step G H := by
  cases h with
  | addTerm => exact Step.addTerm G
  | add a hx hy => exact Step.add G a hx hy

theorem AddReach.reach {G H : St} {k : Nat} (h : AddReach G H k) : Reach G H k := by
  induction h with
  | refl => exact Reach.refl _
  | step _ st ih => exact Reach.step ih st.step

theorem Reach.trans {G H K : St} {j k : Nat} (h1 : Reach G H j) (h2 : Reach H K k) : Reach G K (j + k) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach.step ih st

theorem Reach.single {G H : St} (h : Step G H) : Reach G H 1 := Reach.step (Reach.refl G) h

theorem AddReach.trans {G H K : St} {j k : Nat} (h1 : AddReach G H j) (h2 : AddReach H K k) :
    AddReach G K (j + k) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact AddReach.step ih st

/-! ## Well-formedness and size -/

theorem Step.wf {G H : St} (h : Step G H) (hw : G.WF) : H.WF := by
  cases h with
  | addTerm =>
    intro a ha
    have := hw a ha
    exact ⟨by show a.x < G.n + 1; omega, by show a.y < G.n + 1; omega⟩
  | add a hx hy =>
    intro b hb
    rcases List.mem_cons.1 hb with e | hb'
    · subst e
      exact ⟨hx, hy⟩
    · exact hw b hb'
  | remove a _ =>
    intro b hb
    exact hw b (mem_of_mem_del hb)
  | identify u v hu hv huv =>
    intro b hb
    obtain ⟨c, hc, e⟩ := List.mem_map.1 hb
    subst e
    exact ⟨glue_lt hu hv huv (hw c hc).1, glue_lt hu hv huv (hw c hc).2⟩

theorem Reach.wf {G H : St} {k : Nat} (h : Reach G H k) (hw : G.WF) : H.WF := by
  induction h with
  | refl => exact hw
  | step _ st ih => exact st.wf ih

theorem empty_wf : empty.WF := fun _ h => absurd h List.not_mem_nil

/-- Every change moves the ninth's size by exactly one: up for the two additions, down for a
removal or an identification. -/
theorem Step.size_step {G H : St} (h : Step G H) :
    (H.size = G.size + 1 ∧ AddStep G H) ∨ H.size + 1 = G.size := by
  cases h with
  | addTerm =>
    left
    exact ⟨by simp [St.size, St.addTerm]; omega, AddStep.addTerm G⟩
  | add a hx hy =>
    left
    exact ⟨by simp [St.size, St.add]; omega, AddStep.add G a hx hy⟩
  | remove a ha =>
    right
    have := length_del ha
    simp only [St.size, St.remove]
    omega
  | identify u v hu hv huv =>
    right
    simp only [St.size, St.identify, List.length_map]
    omega

theorem Reach.size_le {G H : St} {k : Nat} (h : Reach G H k) : H.size ≤ G.size + k := by
  induction h with
  | refl => omega
  | step _ st ih =>
    rcases st.size_step with ⟨e, _⟩ | e <;> omega

/-- A sequence that raises the size by its length is a sequence of additions. -/
theorem Reach.additions {G H : St} {k : Nat} (h : Reach G H k) (e : H.size = G.size + k) :
    AddReach G H k := by
  induction h with
  | refl => exact AddReach.refl _
  | step r st ih =>
    have hr := r.size_le
    rcases st.size_step with ⟨e', ad⟩ | e'
    · exact AddReach.step (ih (by omega)) ad
    · exfalso
      omega

theorem AddStep.size {G H : St} (h : AddStep G H) : H.size = G.size + 1 := by
  cases h with
  | addTerm => simp [St.size, St.addTerm]; omega
  | add a _ _ => simp [St.size, St.add]; omega

theorem AddReach.size {G H : St} {k : Nat} (h : AddReach G H k) : H.size = G.size + k := by
  induction h with
  | refl => rfl
  | step _ st ih => rw [st.size, ih]; omega

/-- The number of terms stays positive once positive, for every change of a well-formed state. -/
theorem Step.n_pos {G H : St} (h : Step G H) (hw : G.WF) : 0 < H.n := by
  cases h with
  | addTerm => simp [St.addTerm]
  | add a hx _ => show 0 < G.n; omega
  | remove a ha => show 0 < G.n; have := (hw a ha).1; omega
  | identify u v hu hv huv => show 0 < G.n - 1; omega

theorem Reach.n_pos {G H : St} {k : Nat} (h : Reach G H k) (hw : G.WF) (hn : 0 < G.n) : 0 < H.n := by
  induction h with
  | refl => exact hn
  | step r st _ => exact st.n_pos (r.wf hw)

/-- A well-formed state without terms asserts nothing. -/
theorem eq_empty_of_wf {G : St} (hw : G.WF) (hn : G.n = 0) : G = empty := by
  cases G with
  | mk n A =>
    change n = 0 at hn
    subst hn
    cases A with
    | nil => rfl
    | cons a t =>
      have := (hw a List.mem_cons_self).1
      exact absurd this (Nat.not_lt_zero _)

/-! ## The ninth's sameness at a fixed writing -/

/-- The same ninth state: equally many terms, the same multiplicities (the lists are rearrangements
of each other). -/
def SameState9 (G H : St) : Prop := G.n = H.n ∧ G.A.Perm H.A

theorem SameState9.size {G H : St} (h : SameState9 G H) : G.size = H.size := by
  simp only [St.size, h.1, h.2.length_eq]

end Twentysecond
