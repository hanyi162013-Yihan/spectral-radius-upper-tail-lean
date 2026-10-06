import SpectralRadiusUpperTail.DefectRouteCertificate

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma sum_zero_or_two_unique {α : Type*} [Fintype α] (a : α → ℕ)
    (ha : ∀ i, a i = 0 ∨ a i = 2) (hs : ∑ i, a i = 2) : ∃! i, a i = 2 := by
  classical
  have hp : 0 < ∑ i, a i := by rw [hs]; decide
  obtain ⟨i,_,hi⟩ := Finset.sum_pos_iff.mp hp
  have hi2 : a i = 2 := (ha i).resolve_left (Nat.ne_of_gt hi)
  refine ⟨i,hi2,?_⟩
  intro j hj
  by_contra hji
  have hle : (∑ k ∈ ({i,j} : Finset α), a k) ≤ ∑ k, a k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
  have hij : i ≠ j := Ne.symm hji
  simp only [Finset.sum_pair hij,hi2,hj,hs] at hle
  omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- Each retained entry belongs to exactly one indexed expanded tour. This
counts positions in the tour list, so duplicate-looking tours are distinguished. -/
lemma DefectRouteCertificate.unique_entry_tour {s : Fin (2*r) → Bool}
    {v : Fin (2*r+1) → ι} (c : DefectRouteCertificate s v) (e : ι × ι)
    (he : e ∈ c.treeEntries ∧ entryMultiplicity (orientedWalkEdge s v) e = 2) :
    ∃! i : Fin (expandedDefectRoutes c.segments c.tours).length,
      (((expandedDefectRoutes c.segments c.tours).get i).tokens.map Prod.fst).count e = 2 := by
  let Q := expandedDefectRoutes c.segments c.tours
  let a : Fin Q.length → ℕ := fun i => ((Q.get i).tokens.map Prod.fst).count e
  have ha : ∀ i, a i = 0 ∨ a i = 2 := by
    intro i
    by_cases hm : e ∈ (Q.get i).tokens.map Prod.fst
    · obtain ⟨t,ht,hte⟩ := List.mem_map.mp hm
      right
      change ((Q.get i).tokens.map Prod.fst).count e = 2
      rw [← hte]
      exact c.route_double_entries (Q.get i) (List.get_mem Q i) t ht
    · left
      exact List.count_eq_zero.mpr hm
  have htotal : (Q.flatMap (fun p => p.tokens.map Prod.fst)).count e = 2 := by
    exact (c.total_entry_counts e).trans (if_pos he)
  have hs : ∑ i, a i = 2 := by
    have hh := congrArg (fun J : List (SegmentRoute ι (ι × ι)) =>
      (J.map (fun p => (p.tokens.map Prod.fst).count e)).sum) (List.ofFn_get Q)
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def] at hh
    change (∑ i : Fin Q.length, ((Q.get i).tokens.map Prod.fst).count e) = 2
    rw [hh]
    simpa only [List.count_flatMap,Function.comp_def] using htotal
  exact sum_zero_or_two_unique a ha hs

#print axioms sum_zero_or_two_unique
#print axioms DefectRouteCertificate.unique_entry_tour
end SpectralRadiusUpperTail
