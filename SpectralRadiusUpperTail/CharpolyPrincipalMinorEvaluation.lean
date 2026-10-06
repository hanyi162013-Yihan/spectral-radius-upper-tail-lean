import SpectralRadiusUpperTail.GaussianWeightedPrincipalMinorParseval
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Sum over principal minors grouped by their cardinality. -/
theorem sum_principalMinors_by_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Finset ι → ℝ) :
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
      ∑ s ∈ (Finset.univ : Finset ι).powersetCard k, f s) =
      ∑ s : Finset ι, f s := by
  classical
  calc
    _ = ∑ k ∈ Finset.range (Fintype.card ι + 1),
          ∑ s : Finset ι, if s.card = k then f s else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.powersetCard_eq_filter, Finset.powerset_univ,
          Finset.sum_filter]
    _ = ∑ s : Finset ι,
          ∑ k ∈ Finset.range (Fintype.card ι + 1),
            if s.card = k then f s else 0 := Finset.sum_comm
    _ = ∑ s : Finset ι, f s := by
        apply Finset.sum_congr rfl
        intro s hs
        simp [Finset.mem_range,
          Nat.lt_succ_of_le (Finset.card_le_univ s)]

/-- Characteristic-polynomial evaluation as a weighted sum of all principal minors. -/
theorem charpoly_eval_eq_sum_principalMinors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (x : ℝ) :
    M.charpoly.eval x =
      ∑ s : Finset ι,
        ((-1 : ℝ)^s.card * x^(Fintype.card ι - s.card)) *
          (M.submatrix (Subtype.val : s → ι)
            (Subtype.val : s → ι)).det := by
  classical
  let N := Fintype.card ι
  have hN : M.charpoly.natDegree = N := M.charpoly_natDegree_eq_dim
  rw [Polynomial.eval_eq_sum_range, hN]
  rw [← Finset.sum_range_reflect
    (fun i => M.charpoly.coeff i * x^i) (N+1)]
  simp only [Nat.add_sub_cancel_right]
  let f : Finset ι → ℝ := fun s =>
    ((-1 : ℝ)^s.card * x^(N-s.card)) *
      (M.submatrix (Subtype.val : s → ι)
        (Subtype.val : s → ι)).det
  calc
    (∑ k ∈ Finset.range (N+1), M.charpoly.coeff (N-k) * x^(N-k))
        = ∑ k ∈ Finset.range (N+1),
            ∑ s ∈ (Finset.univ : Finset ι).powersetCard k, f s := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [Matrix.charpoly_coeff_eq_sum_minors M k hkN,
            Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s hs
          have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
          dsimp [f]
          rw [hcard]
          ring
    _ = ∑ s : Finset ι, f s := sum_principalMinors_by_card f
    _ = _ := rfl

end SpectralRadiusUpperTail
