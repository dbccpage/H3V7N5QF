import Twentysecond.State

/-!
# The plain state: the pairs asserted together taken out

For a list of atoms, `split` goes through it once and keeps two lists: the
*plain* part, in which no pair is asserted in both relations, and the pairs
*taken out* — each an `xry` with the `xsy` on the same two terms.  An atom
whose partner is in the plain part so far takes that partner out with it;
otherwise it joins the plain part.

Derived here:
* the list is a rearrangement of its plain part followed by the pairs taken
  out (`perm_split`), and the pairs taken out come as `a`, `a.partner`
  (`Together`), so they are as many `xry` as `xsy` on every pair;
* `count_plain`: the multiplicity of `xqy` in the plain part is the
  multiplicity of `xqy` less that of the same pair in the other relation,
  cut at zero — so the plain part is determined by the *excess*
  `M_r − M_s` at every pair, and is the same for rearranged lists
  (`plain_perm`); no pair is asserted in both relations in it
  (`plain_reduced`);
* `count_together`: the pairs taken out at `xqy` are `min(M_q, M_other)`;
* the plain part of a list with pairs added is the plain part of the list
  (`plain_append_together`), and the plain part of a list asserting no pair in
  both relations is the list (`plain_eq_self`);
* lengths: `length_split`, `Together.even`, `length_plain_le`.
-/

namespace Twentysecond

/-- Pairs asserted together: `a`, then `a.partner`, repeated. -/
inductive Together : List Atom → Prop
  | nil : Together []
  | cons (a : Atom) {M : List Atom} : Together M → Together (a :: a.partner :: M)

/-- One atom joins: it takes its partner out of the plain part if the partner is there. -/
def push (a : Atom) (p : List Atom × List Atom) : List Atom × List Atom :=
  if a.partner ∈ p.1 then (del a.partner p.1, a :: a.partner :: p.2) else (a :: p.1, p.2)

/-- The plain part and the pairs taken out. -/
def split : List Atom → List Atom × List Atom
  | [] => ([], [])
  | a :: l => push a (split l)

/-- The plain part of a list of atoms. -/
def plain (l : List Atom) : List Atom := (split l).1

/-- The pairs taken out of a list of atoms. -/
def together (l : List Atom) : List Atom := (split l).2

theorem plain_nil : plain [] = [] := rfl

theorem plain_cons (a : Atom) (l : List Atom) :
    plain (a :: l) = if a.partner ∈ plain l then del a.partner (plain l) else a :: plain l := by
  show (push a (split l)).1 = _
  unfold push plain
  by_cases h : a.partner ∈ (split l).1 <;> simp [h]

theorem together_cons (a : Atom) (l : List Atom) :
    together (a :: l) = if a.partner ∈ plain l then a :: a.partner :: together l else together l := by
  show (push a (split l)).2 = _
  unfold push plain together
  by_cases h : a.partner ∈ (split l).1 <;> simp [h]

theorem together_together (l : List Atom) : Together (together l) := by
  induction l with
  | nil => exact Together.nil
  | cons a t ih =>
    rw [together_cons]
    by_cases h : a.partner ∈ plain t
    · simp only [h, if_true]
      exact Together.cons a ih
    · simp only [h, if_false]
      exact ih

theorem perm_split (l : List Atom) : l.Perm (plain l ++ together l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a t ih =>
    rw [plain_cons, together_cons]
    by_cases h : a.partner ∈ plain t
    · simp only [h, if_true]
      have e1 : (plain t).Perm (a.partner :: del a.partner (plain t)) := perm_cons_del h
      have e2 : (plain t ++ together t).Perm (a.partner :: (del a.partner (plain t) ++ together t)) :=
        (List.Perm.append e1 (List.Perm.refl _))
      refine (List.Perm.cons a (ih.trans e2)).trans ?_
      refine List.Perm.trans ?_ (List.perm_middle).symm
      refine List.Perm.cons a ?_
      exact (List.perm_middle).symm
    · simp only [h, if_false]
      exact List.Perm.cons a ih

theorem Together.count {M : List Atom} (h : Together M) (b : Atom) : M.count b = M.count b.partner := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    rw [count_cons', count_cons', count_cons', count_cons', ih]
    simp only [Atom.partner_eq_iff, Atom.partner_partner]
    omega

theorem Together.even {M : List Atom} (h : Together M) : ∃ k, M.length = 2 * k := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | cons a _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by simp [hk]; omega⟩

theorem Together.append {M M' : List Atom} (h : Together M) (h' : Together M') : Together (M ++ M') := by
  induction h with
  | nil => exact h'
  | cons a _ ih => exact Together.cons a ih

theorem Together.map {M : List Atom} (h : Together M) (f : Nat → Nat) : Together (M.map (Atom.mapT f)) := by
  induction h with
  | nil => exact Together.nil
  | cons a _ ih =>
    simp only [List.map_cons]
    rw [← Atom.mapT_partner]
    exact Together.cons _ ih

theorem Together.map_partner {M : List Atom} (h : Together M) : Together (M.map Atom.partner) := by
  induction h with
  | nil => exact Together.nil
  | cons a _ ih =>
    simp only [List.map_cons]
    exact Together.cons _ ih

/-- **The plain part counts the excess**, cut at zero. -/
theorem count_plain (l : List Atom) (b : Atom) :
    (plain l).count b = l.count b - l.count b.partner := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih =>
    have hne : a ≠ a.partner := fun e => Atom.partner_ne a e.symm
    have ih_a := ih a
    have ih_p := ih a.partner
    rw [Atom.partner_partner] at ih_p
    rw [plain_cons, count_cons' b a t, count_cons' b.partner a t]
    by_cases h : a.partner ∈ plain t
    · rw [if_pos h]
      have hpos := count_pos_of_mem h
      by_cases e1 : b = a
      · subst e1
        rw [count_del_ne _ hne, ih_a]
        simp [hne]
        omega
      · by_cases e2 : b = a.partner
        · subst e2
          rw [count_del_self, Atom.partner_partner, ih_p]
          simp [hne]
          omega
        · have e3 : a ≠ b.partner := fun e => e2 (by rw [e, Atom.partner_partner])
          rw [count_del_ne _ e2, ih b]
          simp [Ne.symm e1, e3]
    · rw [if_neg h]
      have hz : (plain t).count a.partner = 0 := count_eq_zero_of_not_mem h
      rw [count_cons']
      by_cases e1 : b = a
      · subst e1
        rw [ih_a]
        simp [hne]
        omega
      · by_cases e2 : b = a.partner
        · subst e2
          rw [Atom.partner_partner, ih_p]
          simp [hne]
          omega
        · have e3 : a ≠ b.partner := fun e => e2 (by rw [e, Atom.partner_partner])
          rw [ih b]
          simp [Ne.symm e1, e3]

theorem count_plain_le (l : List Atom) (b : Atom) : (plain l).count b ≤ l.count b := by
  rw [count_plain]
  omega

theorem mem_of_mem_plain {l : List Atom} {b : Atom} (h : b ∈ plain l) : b ∈ l :=
  mem_of_count_pos (Nat.lt_of_lt_of_le (count_pos_of_mem h) (count_plain_le l b))

/-- No pair is asserted in both relations in the plain part. -/
theorem plain_reduced {l : List Atom} {b : Atom} (h : b ∈ plain l) : b.partner ∉ plain l := by
  intro h'
  have c1 := count_pos_of_mem h
  have c2 := count_pos_of_mem h'
  rw [count_plain] at c1 c2
  simp only [Atom.partner_partner] at c2
  omega

/-- The pairs taken out at `xqy`: the smaller of the two multiplicities on that pair. -/
theorem count_together (l : List Atom) (b : Atom) :
    (together l).count b = min (l.count b) (l.count b.partner) := by
  have h := (perm_split l).count_eq b
  rw [List.count_append, count_plain] at h
  omega

/-- Rearranged lists have rearranged plain parts. -/
theorem plain_perm {l l' : List Atom} (h : l.Perm l') : (plain l).Perm (plain l') := by
  apply perm_of_count
  intro b
  rw [count_plain, count_plain, h.count_eq, h.count_eq]

/-- Two lists have the same plain part exactly when they have the same excess at every pair. -/
theorem plain_perm_iff {l l' : List Atom} :
    (plain l).Perm (plain l') ↔ ∀ b, l.count b + l'.count b.partner = l'.count b + l.count b.partner := by
  constructor
  · intro h b
    have e1 := h.count_eq b
    have e2 := h.count_eq b.partner
    rw [count_plain, count_plain] at e1 e2
    simp only [Atom.partner_partner] at e2
    omega
  · intro h
    apply perm_of_count
    intro b
    rw [count_plain, count_plain]
    have := h b
    omega

theorem plain_append_together {l M : List Atom} (h : Together M) : (plain (l ++ M)).Perm (plain l) := by
  apply plain_perm_iff.2
  intro b
  rw [List.count_append, List.count_append, h.count b]
  omega

/-- A list asserting no pair in both relations is its own plain part. -/
theorem plain_eq_self {l : List Atom} (h : ∀ a ∈ l, a.partner ∉ l) : plain l = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ht : ∀ b ∈ t, b.partner ∉ t := fun b hb hp =>
      h b (List.mem_cons_of_mem _ hb) (List.mem_cons_of_mem _ hp)
    have hn : a.partner ∉ plain t := fun m =>
      h a List.mem_cons_self (List.mem_cons_of_mem _ (mem_of_mem_plain m))
    rw [plain_cons, ih ht]
    rw [ih ht] at hn
    simp [hn]

theorem length_split (l : List Atom) : l.length = (plain l).length + (together l).length := by
  rw [(perm_split l).length_eq, List.length_append]

theorem length_plain_le (l : List Atom) : (plain l).length ≤ l.length := by
  rw [length_split l]
  omega

theorem mem_of_mem_together {l : List Atom} {b : Atom} (h : b ∈ together l) : b ∈ l :=
  (perm_split l).symm.mem_iff.1 (List.mem_append_right _ h)

/-- The plain part of the plain part is the plain part. -/
theorem plain_plain (l : List Atom) : plain (plain l) = plain l :=
  plain_eq_self fun _ h => plain_reduced h

/-- Plain parts respect adding one atom in front. -/
theorem plain_cons_perm {l l' : List Atom} (a : Atom) (h : (plain l).Perm (plain l')) :
    (plain (a :: l)).Perm (plain (a :: l')) := by
  apply plain_perm_iff.2
  intro b
  have := plain_perm_iff.1 h b
  rw [count_cons', count_cons', count_cons', count_cons']
  omega

/-- The plain part, moved by a map of terms, is the plain part of the moved list after the pairs
that the map puts together are taken out. -/
theorem plain_map_perm (f : Nat → Nat) (l : List Atom) :
    (plain (l.map (Atom.mapT f))).Perm (plain ((plain l).map (Atom.mapT f))) := by
  have h1 : (l.map (Atom.mapT f)).Perm ((plain l).map (Atom.mapT f) ++ (together l).map (Atom.mapT f)) := by
    rw [← List.map_append]
    exact (perm_split l).map _
  exact (plain_perm h1).trans (plain_append_together ((together_together l).map f))

theorem length_plain_map_le (f : Nat → Nat) (l : List Atom) :
    (plain (l.map (Atom.mapT f))).length ≤ (plain l).length := by
  rw [(plain_map_perm f l).length_eq]
  have := length_plain_le ((plain l).map (Atom.mapT f))
  rw [List.length_map] at this
  exact this

/-- Parity: the plain part and the list differ by an even number of atoms. -/
theorem plain_parity (l : List Atom) : ∃ k, l.length = (plain l).length + 2 * k := by
  obtain ⟨k, hk⟩ := (together_together l).even
  exact ⟨k, by rw [length_split l, hk]⟩

end Twentysecond
