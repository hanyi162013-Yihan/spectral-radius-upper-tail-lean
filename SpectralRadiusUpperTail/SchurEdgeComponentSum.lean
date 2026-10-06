import SpectralRadiusUpperTail.SchurEdgeComponents

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The noncommutative power splits exactly by the number of upper factors. -/
theorem noncomm_edge_component_sum {R : Type*} [Semiring R]
    (D U : R) (k : ℕ) :
    (∑ l ∈ Finset.range (k+1), noncommEdgeComponent D U l k) = (D+U)^k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [noncommEdgeComponent]
    | succ k =>
      rw [Finset.sum_range_succ']
      simp only [noncommEdgeComponent]
      rw [Finset.sum_comm]
      have htail (s : ℕ) (hs : s ∈ Finset.range (k+1)) :
          (∑ l ∈ Finset.range (k+1),
            noncommEdgeComponent D U l (k+1-s-1)) = (D+U)^(k-s) := by
        have he : k+1-s-1 = k-s := by omega
        rw [he]
        have hsub : Finset.range (k-s+1) ⊆ Finset.range (k+1) := by
          exact Finset.range_mono (by omega)
        have hz : ∀ l ∈ Finset.range (k+1), l ∉ Finset.range (k-s+1) →
            noncommEdgeComponent D U l (k-s) = 0 := by
          intro l _ hl
          apply noncommEdgeComponent_zero_of_length_gt
          have := Finset.mem_range.not.mp hl
          have hs' := Finset.mem_range.mp hs
          omega
        rw [(Finset.sum_subset hsub hz).symm]
        exact ih (k-s) (by omega)
      calc
        (∑ s ∈ Finset.range (k+1), ∑ l ∈ Finset.range (k+1),
            D^s * U * noncommEdgeComponent D U l (k+1-s-1)) + D^(k+1)
            = (∑ s ∈ Finset.range (k+1), D^s * U * (D+U)^(k-s)) + D^(k+1) := by
                congr 1
                apply Finset.sum_congr rfl
                intro s hs
                rw [← Finset.mul_sum, htail s hs]
        _ = (D+U)^(k+1) := by
          rw [noncomm_pow_add_duhamel]
          have hsum :
              (∑ s ∈ Finset.range (k+1), D^s * U * (D+U)^(k-s)) =
                ∑ s ∈ Finset.range (k+1), D^s * U * (D+U)^(k+1-s-1) := by
            apply Finset.sum_congr rfl
            intro s _
            have he : k-s = k+1-s-1 := by omega
            rw [he]
          rw [hsum]
          exact add_comm _ _

#print axioms noncomm_edge_component_sum
end SpectralRadiusUpperTail
