/-!
# Atoms, and deleting one occurrence from a list

The twenty-second seed's states are the ninth's: terms, and a multiplicity for
every ordered pair in each of the two relations `r`, `s`.  This package has no
outside library, so the multiplicities are kept as a list of *atoms*
(relation, `x`, `y`), the multiplicity of `xqy` being how often its atom
occurs; the order of the list is not data (two lists that are rearrangements
of each other are one state, `List.Perm`).

The core library's `List.erase` lemmas rest on the axiom of choice (probed with
`#print axioms` on the pinned toolchain: `List.count_erase`,
`List.perm_cons_erase`, `List.Perm.erase`, `List.perm_iff_count`), which the
axiom report of this derivation refuses.  So one-occurrence deletion is
defined here as `del`, and what is used about it is re-proved: its counts, its
length, that a list is a rearrangement of an element followed by the list
with that element deleted, and that two lists with the same counts are
rearrangements of each other (`perm_of_count`).
-/

namespace Twentysecond

/-- The two relations of the seed. -/
inductive Rel where
  | r
  | s
  deriving DecidableEq, Repr

/-- The other relation. -/
def Rel.other : Rel → Rel
  | .r => .s
  | .s => .r

@[simp] theorem Rel.other_other (q : Rel) : q.other.other = q := by cases q <;> rfl

theorem Rel.other_ne (q : Rel) : q.other ≠ q := by cases q <;> decide

/-- One assertion `x q y`, uncounted. -/
structure Atom where
  q : Rel
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

/-- The assertion on the same two terms written with the other relation: `xsy` for `xry`, and the
converse.  It is also what the exchange of the two relations does to an atom. -/
def Atom.partner (a : Atom) : Atom := ⟨a.q.other, a.x, a.y⟩

@[simp] theorem Atom.partner_partner (a : Atom) : a.partner.partner = a := by
  cases a
  simp [Atom.partner]

theorem Atom.partner_ne (a : Atom) : a.partner ≠ a := by
  intro h
  exact Rel.other_ne a.q (congrArg Atom.q h)

theorem Atom.partner_inj {a b : Atom} (h : a.partner = b.partner) : a = b := by
  have := congrArg Atom.partner h
  simpa using this

theorem Atom.eq_partner_comm {a b : Atom} : b = a.partner ↔ a = b.partner := by
  constructor
  · intro h
    rw [h, Atom.partner_partner]
  · intro h
    rw [h, Atom.partner_partner]

theorem Atom.partner_eq_iff {a b : Atom} : a.partner = b ↔ a = b.partner := by
  constructor
  · intro h
    rw [← h, Atom.partner_partner]
  · intro h
    rw [h, Atom.partner_partner]

theorem Atom.partner_eq_partner_iff {a b : Atom} : a.partner = b.partner ↔ a = b :=
  ⟨Atom.partner_inj, fun h => h ▸ rfl⟩

/-! ## Counting -/

variable {α : Type} [DecidableEq α]

theorem count_cons' (a b : α) (l : List α) :
    (b :: l).count a = l.count a + (if b = a then 1 else 0) := by
  rw [List.count_cons]
  by_cases h : b = a
  · subst h
    simp
  · simp [h]

theorem count_cons_self' (a : α) (l : List α) : (a :: l).count a = l.count a + 1 := by
  rw [count_cons']
  simp

theorem count_cons_ne' {a b : α} (l : List α) (h : b ≠ a) : (b :: l).count a = l.count a := by
  rw [count_cons']
  simp [h]

theorem mem_of_count_pos {a : α} {l : List α} (h : 0 < l.count a) : a ∈ l := List.count_pos_iff.1 h

theorem count_pos_of_mem {a : α} {l : List α} (h : a ∈ l) : 0 < l.count a := List.count_pos_iff.2 h

theorem count_eq_zero_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.count a = 0 := by
  cases hc : l.count a with
  | zero => rfl
  | succ k => exact absurd (mem_of_count_pos (by omega)) h

theorem eq_nil_of_count_zero {l : List α} (h : ∀ a, l.count a = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons b t =>
    have := h b
    rw [count_cons_self'] at this
    omega

omit [DecidableEq α] in
theorem length_pos_of_mem' {a : α} {l : List α} (h : a ∈ l) : 0 < l.length := by
  cases l with
  | nil => exact absurd h List.not_mem_nil
  | cons b t =>
    rw [List.length_cons]
    omega

/-! ## Deleting one occurrence -/

/-- The list with its first occurrence of `a` deleted (the list itself if `a` does not occur). -/
def del (a : α) : List α → List α
  | [] => []
  | b :: l => if b = a then l else b :: del a l

@[simp] theorem del_nil (a : α) : del a ([] : List α) = [] := rfl

theorem del_cons_self (a : α) (l : List α) : del a (a :: l) = l := by simp [del]

theorem del_cons_ne {a b : α} (l : List α) (h : b ≠ a) : del a (b :: l) = b :: del a l := by simp [del, h]

theorem count_del_self (a : α) (l : List α) : (del a l).count a = l.count a - 1 := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    by_cases h : b = a
    · subst h
      rw [del_cons_self, count_cons_self']
      omega
    · rw [del_cons_ne _ h, count_cons_ne' _ h, count_cons_ne' _ h, ih]

theorem count_del_ne {a b : α} (l : List α) (h : b ≠ a) : (del a l).count b = l.count b := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    by_cases hc : c = a
    · subst hc
      rw [del_cons_self, count_cons_ne' _ (Ne.symm h)]
    · rw [del_cons_ne _ hc, count_cons', count_cons', ih]

theorem mem_of_mem_del {a b : α} {l : List α} (h : b ∈ del a l) : b ∈ l := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons c t ih =>
    by_cases hc : c = a
    · subst hc
      rw [del_cons_self] at h
      exact List.mem_cons_of_mem _ h
    · rw [del_cons_ne _ hc] at h
      rcases List.mem_cons.1 h with e | h'
      · exact e ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h')

theorem del_of_not_mem {a : α} {l : List α} (h : a ∉ l) : del a l = l := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    have hc : c ≠ a := fun e => h (e ▸ List.mem_cons_self)
    rw [del_cons_ne _ hc, ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem length_del {a : α} {l : List α} (h : a ∈ l) : (del a l).length + 1 = l.length := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons c t ih =>
    by_cases hc : c = a
    · subst hc
      rw [del_cons_self]
      rfl
    · rw [del_cons_ne _ hc]
      rcases List.mem_cons.1 h with e | h'
      · exact absurd e.symm hc
      · simp only [List.length_cons]
        rw [← ih h']

theorem perm_cons_del {a : α} {l : List α} (h : a ∈ l) : l.Perm (a :: del a l) := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons c t ih =>
    by_cases hc : c = a
    · subst hc
      rw [del_cons_self]
    · rw [del_cons_ne _ hc]
      rcases List.mem_cons.1 h with e | h'
      · exact absurd e.symm hc
      · exact (List.Perm.cons c (ih h')).trans (List.Perm.swap a c _)

/-- Two lists with the same counts are rearrangements of each other (proved here without the
axiom of choice). -/
theorem perm_of_count : ∀ {l l' : List α}, (∀ a, l.count a = l'.count a) → l.Perm l'
  | [], l', h => by
    rw [eq_nil_of_count_zero (fun a => (h a).symm)]
  | b :: t, l', h => by
    have hb : b ∈ l' := mem_of_count_pos (by rw [← h b, count_cons_self']; omega)
    refine List.Perm.trans ?_ (perm_cons_del hb).symm
    refine List.Perm.cons b (perm_of_count fun a => ?_)
    by_cases e : a = b
    · subst e
      have := h a
      rw [count_cons_self'] at this
      rw [count_del_self]
      omega
    · have := h a
      rw [count_cons_ne' _ (Ne.symm e)] at this
      rw [count_del_ne _ e, this]

theorem del_perm {a : α} {l l' : List α} (h : l.Perm l') : (del a l).Perm (del a l') := by
  apply perm_of_count
  intro b
  by_cases e : b = a
  · subst e
    rw [count_del_self, count_del_self, h.count_eq]
  · rw [count_del_ne _ e, count_del_ne _ e, h.count_eq]

/-! ## Mapping -/

variable {β : Type} [DecidableEq β]

theorem count_map_of_inj {f : α → β} (hf : ∀ a b, f a = f b → a = b) (a : α) (l : List α) :
    (l.map f).count (f a) = l.count a := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    rw [List.map_cons, count_cons', count_cons', ih]
    by_cases e : c = a
    · subst e
      simp
    · have : f c ≠ f a := fun h => e (hf _ _ h)
      simp [e, this]

omit [DecidableEq α] in
theorem count_map_not_image {f : α → β} (b : β) (hb : ∀ a, f a ≠ b) (l : List α) :
    (l.map f).count b = 0 := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    rw [List.map_cons, count_cons', ih]
    simp [hb c]

theorem map_del_of_inj {f : α → β} (hf : ∀ a b, f a = f b → a = b) (a : α) (l : List α) :
    (del a l).map f = del (f a) (l.map f) := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    by_cases e : c = a
    · subst e
      rw [del_cons_self, List.map_cons, del_cons_self]
    · have : f c ≠ f a := fun h => e (hf _ _ h)
      rw [del_cons_ne _ e, List.map_cons, List.map_cons, del_cons_ne _ this, ih]

theorem perm_of_perm_map_of_inj {f : α → β} (hf : ∀ a b, f a = f b → a = b) {l l' : List α}
    (h : (l.map f).Perm (l'.map f)) : l.Perm l' := by
  apply perm_of_count
  intro a
  rw [← count_map_of_inj hf a l, ← count_map_of_inj hf a l', h.count_eq]

end Twentysecond
