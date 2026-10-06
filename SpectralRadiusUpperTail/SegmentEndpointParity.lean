import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
variable {α V : Type*} [DecidableEq V]

/-- Endpoint incidences count loops twice and retain parallel segments. -/
def segmentEndpointCount (start finish : α → V) (L : List α) (x : V) : ℕ :=
  (L.map (fun a => (if start a = x then 1 else 0) +
    (if finish a = x then 1 else 0))).sum

lemma segmentEndpointCount_cons (start finish : α → V) (a : α) (L : List α) (x : V) :
    segmentEndpointCount start finish (a::L) x =
      (if start a = x then 1 else 0) + (if finish a = x then 1 else 0) +
        segmentEndpointCount start finish L x := by
  simp [segmentEndpointCount]

lemma segmentEndpointCount_perm (start finish : α → V) {L K : List α}
    (h : L.Perm K) (x : V) :
    segmentEndpointCount start finish L x = segmentEndpointCount start finish K x :=
  (h.map _).sum_eq

lemma segmentEndpoint_even_remove_closed (start finish : α → V) (a : α) (L : List α)
    (ha : start a = finish a)
    (h : ∀ x, Even (segmentEndpointCount start finish (a::L) x)) :
    ∀ x, Even (segmentEndpointCount start finish L x) := by
  intro x
  have hx := h x
  rw [segmentEndpointCount_cons,ha] at hx
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at hx ⊢
  split_ifs at hx <;> omega

/-- In an even endpoint multigraph an open segment has another incident segment. -/
lemma segmentEndpoint_exists_incident (start finish : α → V) (a : α) (L : List α)
    (ha : start a ≠ finish a)
    (h : ∀ x, Even (segmentEndpointCount start finish (a::L) x)) :
    ∃ b ∈ L, start b = finish a ∨ finish b = finish a := by
  by_contra hn
  have hz : segmentEndpointCount start finish L (finish a) = 0 := by
    unfold segmentEndpointCount
    apply List.sum_eq_zero
    intro n hn'
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hn'
    have hb' : start b ≠ finish a ∧ finish b ≠ finish a := by
      constructor
      · intro he; exact hn ⟨b,hb,Or.inl he⟩
      · intro he; exact hn ⟨b,hb,Or.inr he⟩
    simp [hb'.1,hb'.2]
  have hx := h (finish a)
  simp [segmentEndpointCount_cons,ha,hz] at hx

/-- Joining incident segments removes exactly two incidences at the joint. -/
lemma segmentEndpoint_merge_even (start finish : α → V) (a b c : α) (L : List α)
    (hab : finish a = start b) (hc1 : start c = start a) (hc2 : finish c = finish b)
    (h : ∀ x, Even (segmentEndpointCount start finish (a::b::L) x)) :
    ∀ x, Even (segmentEndpointCount start finish (c::L) x) := by
  intro x
  have hx := h x
  simp only [segmentEndpointCount_cons,hab,hc1,hc2] at hx ⊢
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at hx ⊢
  split_ifs at hx ⊢ <;> omega

lemma segmentEndpoint_reverse_even (start finish : α → V) (a b c : α) (L : List α)
    (hc1 : start c = finish b) (hc2 : finish c = start b)
    (h : ∀ x, Even (segmentEndpointCount start finish (a::b::L) x)) :
    ∀ x, Even (segmentEndpointCount start finish (a::c::L) x) := by
  intro x
  have hx := h x
  simpa only [segmentEndpointCount_cons,hc1,hc2,Nat.add_comm,Nat.add_left_comm,
    Nat.add_assoc] using hx

#print axioms segmentEndpointCount
#print axioms segmentEndpointCount_cons
#print axioms segmentEndpointCount_perm
#print axioms segmentEndpoint_even_remove_closed
#print axioms segmentEndpoint_exists_incident
#print axioms segmentEndpoint_merge_even
#print axioms segmentEndpoint_reverse_even
end SpectralRadiusUpperTail
