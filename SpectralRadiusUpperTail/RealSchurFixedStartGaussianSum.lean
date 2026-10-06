import SpectralRadiusUpperTail.RealSchurStrictPathGaussian
import SpectralRadiusUpperTail.RealSchurGlobalOrthogonality
import SpectralRadiusUpperTail.SchurFixedStartPathSum
import SpectralRadiusUpperTail.RealSchurFixedStartFamily

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- For a positive number of strict edges, the matrix-power fixed-start
path sum is exactly the sum of the waiting-time Gaussian product-model
terms on the same common array. -/
theorem realSchurFixedStartPathSum_gaussian {N : ℕ} (n k l : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) :
    schurFixedStartPathSum 2 N (l+1) k
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) i j =
      ∑ p : {p : IncreasingBlockPath N (l+1) // p.val 0 = i},
        if p.val.val (Fin.last (l+1)) = j then
          realSchurGlobalWaitingSum n k B ⟨l+1,p.val⟩ z else 0 := by
  unfold schurFixedStartPathSum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hj : p.val.val (Fin.last (l+1)) = j
  · simp only [hj, if_pos]
    rw [realSchurGlobalWaitingSum_eq]
    apply Finset.sum_congr rfl
    intro m hm
    exact realSchurStrictPathTerm_gaussian n l B z p.val m.val
  · simp only [hj, if_neg]
    simp

#print axioms realSchurFixedStartPathSum_gaussian
end SpectralRadiusUpperTail
