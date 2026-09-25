import Twentysecond.Same

/-!
# The fewest changes to a result

`phi G`: the terms of `G` plus the assertions of its plain part — the ninth's
size of the plain state (`paper/ninth/`, D4: the fewest changes to a state is
its size).  Derived here:
* `phi` is the same for two states that are one result (`Same.phi`);
* every change raises `phi` by at most one, and an identification lowers it
  by at least one (`Step.phi_le`, `Step.phi_identify`);
* from the empty state `phi G` additions reach the plain state of `G`
  (`reach_plainSt`);
* so **the fewest changes to the result of `G` is `phi G`**
  (`fewest_changes`);
* the ninth's size of any state of the result is `phi` plus the atoms of the
  pairs asserted together (`size_eq_phi_add_together`): the ninth's cost
  survives exactly on states asserting no pair in both relations;
* a sequence from the empty state as short as `phi` of its end is additions
  only and ends at a state asserting no pair in both relations
  (`shortest_additions`), and each of its prefixes is as short as the
  prefix's end allows (`shortest_prefix`).
-/

namespace Twentysecond

/-- Terms plus the assertions of the plain part. -/
def phi (G : St) : Nat := G.n + (plain G.A).length

theorem Same.phi {G H : St} (h : Same G H) : phi G = phi H := by
  simp only [Twentysecond.phi, h.1, h.2.length_eq]

theorem phi_empty : phi empty = 0 := rfl

theorem phi_le_size (G : St) : phi G ≤ G.size := by
  have := length_plain_le G.A
  simp only [Twentysecond.phi, St.size]
  omega

/-- The ninth's size of a state is `phi` plus the atoms of its pairs asserted together. -/
theorem size_eq_phi_add_together (G : St) : G.size = phi G + (together G.A).length := by
  have := length_split G.A
  simp only [Twentysecond.phi, St.size]
  omega

theorem length_plain_cons (a : Atom) (l : List Atom) :
    (a.partner ∈ plain l ∧ (plain (a :: l)).length + 1 = (plain l).length) ∨
    (a.partner ∉ plain l ∧ (plain (a :: l)).length = (plain l).length + 1) := by
  rw [plain_cons]
  by_cases h : a.partner ∈ plain l
  · left
    rw [if_pos h]
    exact ⟨h, length_del h⟩
  · right
    rw [if_neg h]
    exact ⟨h, rfl⟩

theorem Step.phi_le {G H : St} (st : Step G H) : phi H ≤ phi G + 1 := by
  cases st with
  | addTerm =>
    simp only [Twentysecond.phi, St.addTerm]
    omega
  | add a _ _ =>
    simp only [Twentysecond.phi, St.add]
    rcases length_plain_cons a G.A with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  | remove a ha =>
    simp only [Twentysecond.phi, St.remove]
    have e := (plain_perm (perm_cons_del ha)).length_eq
    rcases length_plain_cons a (del a G.A) with ⟨_, e'⟩ | ⟨_, e'⟩ <;> omega
  | identify u v hu hv huv =>
    simp only [Twentysecond.phi, St.identify]
    have := length_plain_map_le (glue G.n u v) G.A
    omega

theorem Step.phi_identify {G : St} {u v : Nat} (hv : v < G.n) :
    phi (G.identify u v) + 1 ≤ phi G := by
  simp only [Twentysecond.phi, St.identify]
  have := length_plain_map_le (glue G.n u v) G.A
  omega

theorem Reach.phi_le {G H : St} {k : Nat} (h : Reach G H k) : phi H ≤ phi G + k := by
  induction h with
  | refl => omega
  | step _ st ih =>
    have := st.phi_le
    omega

/-- The terms one by one from the empty state. -/
theorem addReach_terms (n : Nat) : AddReach empty ⟨n, []⟩ n := by
  induction n with
  | zero => exact AddReach.refl _
  | succ m ih => exact AddReach.step ih (AddStep.addTerm ⟨m, []⟩)

/-- The assertions of a list one by one, on `n` terms. -/
theorem addReach_atoms (n : Nat) :
    ∀ L : List Atom, (∀ a ∈ L, a.x < n ∧ a.y < n) → AddReach ⟨n, []⟩ ⟨n, L⟩ L.length
  | [], _ => AddReach.refl _
  | a :: L, h => by
    have r := addReach_atoms n L (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact AddReach.step r (AddStep.add ⟨n, L⟩ a (h a List.mem_cons_self).1 (h a List.mem_cons_self).2)

/-- From the empty state, `phi G` additions reach the plain state of `G`. -/
theorem reach_plainSt {G : St} (hw : G.WF) : AddReach empty G.plainSt (phi G) := by
  have h1 := addReach_terms G.n
  have h2 := addReach_atoms G.n (plain G.A) (fun a ha => hw a (mem_of_mem_plain ha))
  have := AddReach.trans h1 h2
  simpa [Twentysecond.phi, St.plainSt] using this

/-- **The fewest changes from what is given (the empty state) to the result of a well-formed state
`G` is `phi G`**: some state of the result is reached in `phi G` changes, and no state of the result
in fewer. -/
theorem fewest_changes {G : St} (hw : G.WF) :
    (∃ H, Same H G ∧ Reach empty H (phi G)) ∧ ∀ H k, Same H G → Reach empty H k → phi G ≤ k := by
  refine ⟨⟨G.plainSt, (same_plainSt G).symm, (reach_plainSt hw).reach⟩, ?_⟩
  intro H k hs r
  have := r.phi_le
  rw [phi_empty, hs.phi] at this
  omega

theorem size_empty : empty.size = 0 := rfl

/-- **A shortest sequence is additions only and ends at a state asserting no pair in both
relations.** -/
theorem shortest_additions {H : St} {k : Nat} (r : Reach empty H k) (hk : k = phi H) :
    AddReach empty H k ∧ together H.A = [] := by
  have hs := r.size_le
  have hp := phi_le_size H
  have he := size_eq_phi_add_together H
  rw [size_empty] at hs
  refine ⟨r.additions (by rw [size_empty]; omega), ?_⟩
  have : (together H.A).length = 0 := by omega
  cases hl : together H.A with
  | nil => rfl
  | cons b t =>
    rw [hl, List.length_cons] at this
    omega

/-- Every prefix of a shortest sequence is shortest. -/
theorem shortest_prefix {K H : St} {j : Nat} (r : Reach empty K j) (st : Step K H) (hk : j + 1 = phi H) :
    j = phi K := by
  have h1 := st.phi_le
  have h2 := r.phi_le
  rw [phi_empty] at h2
  omega

/-- The one-term result asserting `asa` once costs two changes. -/
theorem phi_asa : phi ⟨1, [⟨.s, 0, 0⟩]⟩ = 2 := rfl

/-- The cost and the ninth's size have the same parity. -/
theorem phi_parity_size (G : St) : phi G % 2 = G.size % 2 := by
  obtain ⟨k, hk⟩ := plain_parity G.A
  simp only [phi, St.size]
  omega

/-- **Every change changes the parity of the cost**: no change keeps a result in its round. -/
theorem Step.phi_parity {G H : St} (st : Step G H) : (phi G + phi H) % 2 = 1 := by
  have h1 := phi_parity_size G
  have h2 := phi_parity_size H
  rcases st.size_step with ⟨e, _⟩ | e <;> omega

/-- **No single change returns to the result it started from.** -/
theorem Step.not_same {G H : St} (st : Step G H) : ¬ Same G H := by
  intro h
  have := st.phi_parity
  rw [h.phi] at this
  omega

/-- A sequence of additions along which every state asserts no pair in both relations. -/
inductive PlainReach : St → St → Nat → Prop
  | refl (G : St) : together G.A = [] → PlainReach G G 0
  | step {G H K : St} {k : Nat} : PlainReach G H k → AddStep H K → together K.A = [] → PlainReach G K (k + 1)

theorem shortest_all_plain_aux {G H : St} {k : Nat} (hG : G = empty) (r : Reach G H k) (hk : k = phi H) :
    PlainReach G H k := by
  induction r with
  | refl => subst hG; exact PlainReach.refl _ rfl
  | @step K H' j r st ih =>
    subst hG
    have hj : j = phi K := shortest_prefix r st hk
    have hK := (shortest_additions r hj).2
    have hH := (shortest_additions (Reach.step r st) hk).2
    have sK := size_eq_phi_add_together K
    have sH := size_eq_phi_add_together H'
    rw [hK, List.length_nil] at sK
    rw [hH, List.length_nil] at sH
    rcases st.size_step with ⟨_, ad⟩ | e
    · exact PlainReach.step (ih hj) ad hH
    · exfalso
      omega

/-- **Every state along a shortest sequence asserts no pair in both relations**: a shortest sequence
never adds both relations at one pair. -/
theorem shortest_all_plain {H : St} {k : Nat} (r : Reach empty H k) (hk : k = phi H) : PlainReach empty H k :=
  shortest_all_plain_aux rfl r hk

end Twentysecond
