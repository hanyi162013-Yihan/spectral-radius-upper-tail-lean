import SpectralRadiusUpperTail.TreeSegmentCutEntry
import SpectralRadiusUpperTail.ListFlatMapCountBound

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma route_entry_support_of_total_count (T : Finset (V × V))
    (Q : List (SegmentRoute V (V × V)))
    (hz : ∀ e, e ∉ T → (Q.flatMap (fun p => p.tokens.map Prod.fst)).count e = 0)
    (p : SegmentRoute V (V × V)) (hp : p ∈ Q) (t : (V × V) × Bool) (ht : t ∈ p.tokens) :
    t.1 ∈ T := by
  by_contra hn
  have hpos : 0 < (p.tokens.map Prod.fst).count t.1 :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩)
  have hle := list_count_le_flatMap_of_mem (fun p : SegmentRoute V (V × V) =>
    p.tokens.map Prod.fst) Q p hp t.1
  have hzero := hz t.1 hn
  omega

/-- With total multiplicity at most two, a closed route in an oriented tree
contains either both occurrences of an entry or neither occurrence. -/
lemma closedTreeRoutes_entry_zero_or_two (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (Q : List (SegmentRoute V (V × V)))
    (hQ : ∀ p ∈ Q, p.Valid (fun e => e) ∧ p.start = p.finish)
    (hT : ∀ p ∈ Q, ∀ t ∈ p.tokens, t.1 ∈ T)
    (hc : ∀ e, (Q.flatMap (fun p => p.tokens.map Prod.fst)).count e ≤ 2)
    (p : SegmentRoute V (V × V)) (hp : p ∈ Q) (e : V × V) :
    (p.tokens.map Prod.fst).count e = 0 ∨ (p.tokens.map Prod.fst).count e = 2 := by
  have he := closedTreeRoute_entry_even T ht hno p (hQ p hp).1.1 (hQ p hp).2 (hT p hp) e
  have hle := list_count_le_flatMap_of_mem (fun p : SegmentRoute V (V × V) =>
    p.tokens.map Prod.fst) Q p hp e
  have htwo := hc e
  rw [even_iff_two_dvd,Nat.dvd_iff_mod_eq_zero] at he
  omega

#print axioms route_entry_support_of_total_count
#print axioms closedTreeRoutes_entry_zero_or_two
end SpectralRadiusUpperTail
