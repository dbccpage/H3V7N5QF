import Twentysecond.Reach

/-!
# The exchange of the two relations

Exchanging `r` with `s` in every assertion (`St.swap`: every atom replaced by
its partner) is a symmetry of the ninth (`paper/ninth/`, D16).  Here: it
turns every excess into its negative (`excess_swap`), carries the plain part
to the plain part (`plain_swap`), keeps this seed's sameness both ways
(`same_swap_iff`) and the cost (`phi_swap`), and carries every change to a
change of the same kind (`Step.swap`).  So it is a symmetry of this seed's
results, its cost and its reachability.
-/

namespace Twentysecond

/-- The two relations exchanged. -/
def St.swap (G : St) : St := ⟨G.n, G.A.map Atom.partner⟩

theorem partner_injective : ∀ a b : Atom, a.partner = b.partner → a = b := fun _ _ h => Atom.partner_inj h

theorem mem_map_partner {a : Atom} {l : List Atom} : a ∈ l.map Atom.partner ↔ a.partner ∈ l := by
  constructor
  · intro h
    obtain ⟨c, hc, e⟩ := List.mem_map.1 h
    subst e
    rwa [Atom.partner_partner]
  · intro h
    have := List.mem_map_of_mem (f := Atom.partner) h
    rwa [Atom.partner_partner] at this

theorem plain_swap (l : List Atom) : plain (l.map Atom.partner) = (plain l).map Atom.partner := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, plain_cons, plain_cons, ih, Atom.partner_partner]
    by_cases h : a.partner ∈ plain t
    · have h' : a ∈ (plain t).map Atom.partner := mem_map_partner.2 h
      rw [if_pos h', if_pos h]
      have := map_del_of_inj partner_injective a.partner (plain t)
      rw [Atom.partner_partner] at this
      exact this.symm
    · have h' : a ∉ (plain t).map Atom.partner := fun m => h (mem_map_partner.1 m)
      rw [if_neg h', if_neg h]
      rfl

theorem swap_swap (G : St) : G.swap.swap = G := by
  cases G with
  | mk n A =>
    simp only [St.swap, List.map_map]
    have : (Atom.partner ∘ Atom.partner) = id := funext fun a => Atom.partner_partner a
    rw [this, List.map_id]

theorem Same.swap {G H : St} (h : Same G H) : Same G.swap H.swap :=
  ⟨h.1, by simp only [St.swap, plain_swap]; exact h.2.map _⟩

/-- The exchange keeps this seed's sameness, both ways. -/
theorem same_swap_iff {G H : St} : Same G H ↔ Same G.swap H.swap := by
  constructor
  · exact Same.swap
  · intro h
    have := h.swap
    rwa [swap_swap, swap_swap] at this

/-- The exchange keeps the cost. -/
theorem phi_swap (G : St) : phi G.swap = phi G := by
  simp only [phi, St.swap, plain_swap, List.length_map]

/-- The exchange turns every excess into its negative. -/
theorem excess_swap (G : St) (x y : Nat) : excess G.swap x y = - excess G x y := by
  simp only [excess, St.swap]
  have e1 : (G.A.map Atom.partner).count ⟨.r, x, y⟩ = G.A.count ⟨.s, x, y⟩ :=
    count_map_of_inj partner_injective ⟨.s, x, y⟩ G.A
  have e2 : (G.A.map Atom.partner).count ⟨.s, x, y⟩ = G.A.count ⟨.r, x, y⟩ :=
    count_map_of_inj partner_injective ⟨.r, x, y⟩ G.A
  rw [e1, e2]
  omega

theorem swap_wf {G : St} (hw : G.WF) : G.swap.WF := by
  intro a ha
  have := hw a.partner (mem_map_partner.1 ha)
  exact this

/-- The exchange carries every change to a change of the same kind. -/
theorem Step.swap {G H : St} (st : Step G H) : Step G.swap H.swap := by
  cases st with
  | addTerm => exact Step.addTerm G.swap
  | add a hx hy => exact Step.add G.swap a.partner hx hy
  | remove a ha =>
    have e : (G.remove a).swap = G.swap.remove a.partner := by
      simp only [St.swap, St.remove, map_del_of_inj partner_injective]
    rw [e]
    exact Step.remove G.swap a.partner (List.mem_map_of_mem ha)
  | identify u v hu hv huv =>
    have e : (G.identify u v).swap = G.swap.identify u v := by
      simp only [St.swap, St.identify, List.map_map]
      rfl
    rw [e]
    exact Step.identify G.swap u v hu hv huv

end Twentysecond
