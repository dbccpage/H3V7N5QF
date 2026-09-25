import Twentythird

/-!
# Filled triples, the states carrying them, and the five kinds of change

The twenty-fifth seed adds a fifth kind of change, "filling three different
terms", and one sentence: "Three filled terms `x`, `y`, `z` balance when,
going from `x` to `y` to `z` and back to `x`, as many assertions are written
with `r` as with `s`, each counted as often as it is asserted; for every
result, record which filled terms balance."

Readings of the paper (§3):
* C-F1: a state carries its filled triples (`FSt`: the twenty-second's `St`
  and a list of triples); filling three different terms makes them a filled
  triple and changes nothing else; filling a triple already filled is not a
  change.
* C-O1: a filled triple keeps the order in which its terms are gone round;
  `x, y, z` is `y, z, x` and `z, x, y`.  It is written from its least term
  (`Tri.norm`); `x, z, y` is another triple.
* C-I1: identifying two terms replaces both by one term in every filled triple
  too (`carry`): a triple left without three different terms is dropped, two
  that become one are one (`nub`).

Derived here: the normal form is idempotent and keeps the terms, their
difference and the terms being below `n` (`Tri.norm_norm`, `Tri.norm_within`,
`Tri.norm_distinct`); every change keeps a state well formed (`Step25.wf`); the
twenty-third's states are the states with nothing filled (`embed`), and every
change of the twenty-third is carried to the same change here
(`Step.embed25`, `Reach.embed25`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

/-- Three terms, in the order they are gone round. -/
structure Tri where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

namespace Tri

/-- The same way round, written from its least term. -/
def norm (t : Tri) : Tri :=
  if t.x ≤ t.y then (if t.x ≤ t.z then t else ⟨t.z, t.x, t.y⟩)
  else (if t.y ≤ t.z then ⟨t.y, t.z, t.x⟩ else ⟨t.z, t.x, t.y⟩)

/-- Three different terms. -/
def Distinct (t : Tri) : Prop := t.x ≠ t.y ∧ t.y ≠ t.z ∧ t.x ≠ t.z

instance (t : Tri) : Decidable t.Distinct := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Three terms of a state with `n` terms. -/
def Within (n : Nat) (t : Tri) : Prop := t.x < n ∧ t.y < n ∧ t.z < n

instance (n : Nat) (t : Tri) : Decidable (t.Within n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The terms moved by `f`, the order kept. -/
def map (f : Nat → Nat) (t : Tri) : Tri := ⟨f t.x, f t.y, f t.z⟩

/-- Going round from the next term. -/
def rot (t : Tri) : Tri := ⟨t.y, t.z, t.x⟩

theorem norm_cases (t : Tri) : t.norm = t ∨ t.norm = t.rot ∨ t.norm = t.rot.rot := by
  unfold norm rot
  by_cases h1 : t.x ≤ t.y
  · by_cases h2 : t.x ≤ t.z
    · rw [if_pos h1, if_pos h2]; exact Or.inl rfl
    · rw [if_pos h1, if_neg h2]; exact Or.inr (Or.inr rfl)
  · by_cases h3 : t.y ≤ t.z
    · rw [if_neg h1, if_pos h3]; exact Or.inr (Or.inl rfl)
    · rw [if_neg h1, if_neg h3]; exact Or.inr (Or.inr rfl)

theorem within_rot {n : Nat} {t : Tri} (h : t.Within n) : t.rot.Within n := ⟨h.2.1, h.2.2, h.1⟩

theorem distinct_rot {t : Tri} (h : t.Distinct) : t.rot.Distinct :=
  ⟨h.2.1, fun e => h.2.2 e.symm, fun e => h.1 e.symm⟩

theorem norm_within {n : Nat} {t : Tri} (h : t.Within n) : t.norm.Within n := by
  rcases norm_cases t with e | e | e <;> rw [e]
  · exact h
  · exact within_rot h
  · exact within_rot (within_rot h)

theorem norm_distinct {t : Tri} (h : t.Distinct) : t.norm.Distinct := by
  rcases norm_cases t with e | e | e <;> rw [e]
  · exact h
  · exact distinct_rot h
  · exact distinct_rot (distinct_rot h)

/-- A triple written from its least term is its own normal form. -/
theorem norm_eq_self {t : Tri} (h1 : t.x ≤ t.y) (h2 : t.x ≤ t.z) : t.norm = t := by
  unfold norm
  rw [if_pos h1, if_pos h2]

theorem norm_least (t : Tri) : t.norm.x ≤ t.norm.y ∧ t.norm.x ≤ t.norm.z := by
  unfold norm
  by_cases h1 : t.x ≤ t.y
  · by_cases h2 : t.x ≤ t.z
    · rw [if_pos h1, if_pos h2]; exact ⟨h1, h2⟩
    · rw [if_pos h1, if_neg h2]; exact ⟨by show t.z ≤ t.x; omega, by show t.z ≤ t.y; omega⟩
  · by_cases h3 : t.y ≤ t.z
    · rw [if_neg h1, if_pos h3]; exact ⟨h3, by show t.y ≤ t.x; omega⟩
    · rw [if_neg h1, if_neg h3]; exact ⟨by show t.z ≤ t.x; omega, by show t.z ≤ t.y; omega⟩

/-- **The normal form is idempotent.** -/
theorem norm_norm (t : Tri) : t.norm.norm = t.norm := norm_eq_self (norm_least t).1 (norm_least t).2

theorem norm_mk (x y z : Nat) : (⟨x, y, z⟩ : Tri).norm =
    if x ≤ y then (if x ≤ z then ⟨x, y, z⟩ else ⟨z, x, y⟩) else (if y ≤ z then ⟨y, z, x⟩ else ⟨z, x, y⟩) := rfl

/-- For three different terms, going round from another term has the same normal form. -/
theorem norm_rot {t : Tri} (h : t.Distinct) : t.rot.norm = t.norm := by
  obtain ⟨x, y, z⟩ := t
  have hxy : x ≠ y := h.1
  have hyz : y ≠ z := h.2.1
  have hxz : x ≠ z := h.2.2
  show (⟨y, z, x⟩ : Tri).norm = (⟨x, y, z⟩ : Tri).norm
  rw [norm_mk, norm_mk]
  by_cases a : y ≤ z <;> by_cases b : y ≤ x <;> by_cases c : x ≤ y <;> by_cases d : x ≤ z <;>
    by_cases e : z ≤ x <;> simp only [a, b, c, d, e, if_true, if_false] <;>
    first | rfl | (exfalso; omega)

end Tri

/-- A state of the seed: the twenty-second's state and its filled triples. -/
structure FSt where
  G : St
  F : List Tri

/-- The list with later copies of a triple taken out. -/
def nub : List Tri → List Tri
  | [] => []
  | t :: l => if t ∈ l then nub l else t :: nub l

theorem mem_nub {t : Tri} : ∀ {l : List Tri}, t ∈ nub l ↔ t ∈ l
  | [] => Iff.rfl
  | s :: l => by
    unfold nub
    by_cases h : s ∈ l
    · rw [if_pos h, mem_nub]
      constructor
      · exact List.mem_cons_of_mem _
      · intro m
        rcases List.mem_cons.1 m with e | m'
        · exact e ▸ h
        · exact m'
    · rw [if_neg h, List.mem_cons, List.mem_cons, mem_nub]

theorem nub_nodup : ∀ l : List Tri, (nub l).Nodup
  | [] => List.nodup_nil
  | s :: l => by
    unfold nub
    by_cases h : s ∈ l
    · rw [if_pos h]
      exact nub_nodup l
    · rw [if_neg h]
      exact List.nodup_cons.2 ⟨fun m => h (mem_nub.1 m), nub_nodup l⟩

theorem length_nub_le : ∀ l : List Tri, (nub l).length ≤ l.length
  | [] => Nat.le_refl _
  | s :: l => by
    unfold nub
    by_cases h : s ∈ l
    · rw [if_pos h]
      have := length_nub_le l
      simp only [List.length_cons]
      omega
    · rw [if_neg h]
      have := length_nub_le l
      simp only [List.length_cons]
      omega

/-- The filled triples after identifying `u` and `v` in a state with `n` terms (reading C-I1). -/
def carry (n u v : Nat) (F : List Tri) : List Tri :=
  nub (((F.map (Tri.map (glue n u v))).filter (fun t => decide t.Distinct)).map Tri.norm)

theorem length_carry_le (n u v : Nat) (F : List Tri) : (carry n u v F).length ≤ F.length := by
  unfold carry
  have a := length_nub_le (((F.map (Tri.map (glue n u v))).filter (fun t => decide t.Distinct)).map Tri.norm)
  have b := List.length_filter_le (fun t => decide t.Distinct) (F.map (Tri.map (glue n u v)))
  rw [List.length_map] at a b
  omega

theorem carry_nil (n u v : Nat) : carry n u v [] = [] := rfl

theorem mem_carry {n u v : Nat} {F : List Tri} {t : Tri} (h : t ∈ carry n u v F) :
    ∃ s ∈ F, (s.map (glue n u v)).Distinct ∧ t = (s.map (glue n u v)).norm := by
  unfold carry at h
  obtain ⟨w, hw, e⟩ := List.mem_map.1 (mem_nub.1 h)
  obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
  obtain ⟨s, hs, e'⟩ := List.mem_map.1 hw1
  subst e'
  exact ⟨s, hs, of_decide_eq_true hw2, e.symm⟩

namespace FSt

/-- Well formed: the assertions between terms that are there; every filled triple three different terms
of the state, written from its least term, and listed once. -/
def WF (A : FSt) : Prop :=
  A.G.WF ∧ (∀ t ∈ A.F, t.Within A.G.n ∧ t.Distinct ∧ t.norm = t) ∧ A.F.Nodup

def addTerm (A : FSt) : FSt := ⟨A.G.addTerm, A.F⟩

def add (A : FSt) (a : Atom) : FSt := ⟨A.G.add a, A.F⟩

def remove (A : FSt) (a : Atom) : FSt := ⟨A.G.remove a, A.F⟩

def identify (A : FSt) (u v : Nat) : FSt := ⟨A.G.identify u v, carry A.G.n u v A.F⟩

/-- Filling three terms: the triple, written from its least term, joins the filled triples. -/
def fill (A : FSt) (t : Tri) : FSt := ⟨A.G, t.norm :: A.F⟩

end FSt

/-- What is given: no terms, nothing asserted, nothing filled. -/
def empty25 : FSt := ⟨empty, []⟩

/-- A state of the twenty-third seed, with nothing filled. -/
def embed (G : St) : FSt := ⟨G, []⟩

/-- One change of the seed: the four kinds of the twenty-third, the filled triples carried, or a filling. -/
inductive Step25 : FSt → FSt → Prop
  | addTerm (A : FSt) : Step25 A A.addTerm
  | add (A : FSt) (a : Atom) (hx : a.x < A.G.n) (hy : a.y < A.G.n) : Step25 A (A.add a)
  | remove (A : FSt) (a : Atom) (h : a ∈ A.G.A) : Step25 A (A.remove a)
  | identify (A : FSt) (u v : Nat) (hu : u < A.G.n) (hv : v < A.G.n) (huv : u ≠ v) : Step25 A (A.identify u v)
  | fill (A : FSt) (t : Tri) (hw : t.Within A.G.n) (hd : t.Distinct) (hn : t.norm ∉ A.F) : Step25 A (A.fill t)

/-- `Reach25 A B k`: `B` is reached from `A` by `k` changes. -/
inductive Reach25 : FSt → FSt → Nat → Prop
  | refl (A : FSt) : Reach25 A A 0
  | step {A B C : FSt} {k : Nat} : Reach25 A B k → Step25 B C → Reach25 A C (k + 1)

theorem Reach25.trans {A B C : FSt} {j k : Nat} (h1 : Reach25 A B j) (h2 : Reach25 B C k) :
    Reach25 A C (j + k) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach25.step ih st

theorem Reach25.single {A B : FSt} (h : Step25 A B) : Reach25 A B 1 := Reach25.step (Reach25.refl A) h

/-! ## Well-formedness is kept -/

theorem within_glue {n u v : Nat} (hu : u < n) (hv : v < n) (huv : u ≠ v) {s : Tri} (hs : s.Within n) :
    (s.map (glue n u v)).Within (n - 1) :=
  ⟨glue_lt hu hv huv hs.1, glue_lt hu hv huv hs.2.1, glue_lt hu hv huv hs.2.2⟩

theorem carry_wf {n u v : Nat} (hu : u < n) (hv : v < n) (huv : u ≠ v) {F : List Tri}
    (hF : ∀ t ∈ F, t.Within n) : ∀ t ∈ carry n u v F, t.Within (n - 1) ∧ t.Distinct ∧ t.norm = t := by
  intro t ht
  obtain ⟨s, hs, hd, e⟩ := mem_carry ht
  subst e
  exact ⟨Tri.norm_within (within_glue hu hv huv (hF s hs)), Tri.norm_distinct hd, Tri.norm_norm _⟩

theorem Step25.wf {A B : FSt} (h : Step25 A B) (hw : A.WF) : B.WF := by
  obtain ⟨hG, hF, hN⟩ := hw
  cases h with
  | addTerm =>
    refine ⟨(Step.addTerm A.G).wf hG, fun t ht => ?_, hN⟩
    obtain ⟨⟨a, b, c⟩, d, e⟩ := hF t ht
    exact ⟨⟨by show t.x < A.G.n + 1; omega, by show t.y < A.G.n + 1; omega, by show t.z < A.G.n + 1; omega⟩, d, e⟩
  | add a hx hy => exact ⟨(Step.add A.G a hx hy).wf hG, hF, hN⟩
  | remove a ha => exact ⟨(Step.remove A.G a ha).wf hG, hF, hN⟩
  | identify u v hu hv huv =>
    exact ⟨(Step.identify A.G u v hu hv huv).wf hG,
      carry_wf hu hv huv (fun t ht => (hF t ht).1), nub_nodup _⟩
  | fill t hwt hd hn =>
    refine ⟨hG, fun s hs => ?_, List.nodup_cons.2 ⟨hn, hN⟩⟩
    rcases List.mem_cons.1 hs with e | hs'
    · subst e
      exact ⟨Tri.norm_within hwt, Tri.norm_distinct hd, Tri.norm_norm t⟩
    · exact hF s hs'

theorem Reach25.wf {A B : FSt} {k : Nat} (h : Reach25 A B k) (hw : A.WF) : B.WF := by
  induction h with
  | refl => exact hw
  | step _ st ih => exact st.wf ih

theorem empty25_wf : empty25.WF := ⟨empty_wf, fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩

theorem embed_wf {G : St} (hw : G.WF) : (embed G).WF := ⟨hw, fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩

/-- A well-formed state with fewer than three terms has nothing filled. -/
theorem nothing_filled_of_lt_three {A : FSt} (hw : A.WF) (hn : A.G.n < 3) : A.F = [] := by
  cases e : A.F with
  | nil => rfl
  | cons t l =>
    have := hw.2.1 t (by rw [e]; exact List.mem_cons_self)
    obtain ⟨⟨a, b, c⟩, ⟨d1, d2, d3⟩, _⟩ := this
    exfalso
    omega

/-! ## The twenty-third's states and changes, carried -/

/-- **Every change of the twenty-third is carried to the same change here**, nothing being filled. -/
theorem embed_step {G H : St} (h : Step G H) : Step25 (embed G) (embed H) := by
  cases h with
  | addTerm => exact Step25.addTerm (embed G)
  | add a hx hy => exact Step25.add (embed G) a hx hy
  | remove a ha => exact Step25.remove (embed G) a ha
  | identify u v hu hv huv => exact Step25.identify (embed G) u v hu hv huv

theorem embed_reach {G H : St} {k : Nat} (h : Reach G H k) : Reach25 (embed G) (embed H) k := by
  induction h with
  | refl => exact Reach25.refl _
  | step _ st ih => exact Reach25.step ih (embed_step st)

end Twentyfifth
