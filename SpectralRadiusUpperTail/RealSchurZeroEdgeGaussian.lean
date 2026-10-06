import SpectralRadiusUpperTail.RealSchurZeroEdgePath
import SpectralRadiusUpperTail.RealSchurGlobalOrthogonality
import SpectralRadiusUpperTail.RealSchurFixedStartFamily

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The zero-bridge path term agrees with the global Gaussian path model
for positive total power. -/
theorem realSchurZeroEdgeTerm_gaussian {N : ℕ} (n k : ℕ) (hk : 0 < k)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (p : IncreasingBlockPath N 0) (m : SchurWaitingTimes k 0) :
    schurStrictPathTerm 2 N 0
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) p.val m.val =
      (1/Real.sqrt n)^0 •
        schurPathMatrix (⟨0,p⟩ : AnyIncreasingPath N)
          (fun j => realSchurDataPower (B (p.val j)) (m.val j)
            (z.1 (p.val j))) z.2 := by
  have hm : m.val 0 = k := by simpa using m.property
  have hmpos : 0 < m.val 0 := by omega
  rw [realSchurZeroEdgePath_positive n B z p.val m.val hmpos]
  simp [schurPathMatrix, gaussianMatrixChain]

/-- Fixed-start zero-edge path sums match the global waiting-time model. -/
theorem realSchurFixedStartPathSum_zero_gaussian {N : ℕ}
    (n k : ℕ) (hk : 0 < k) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) :
    schurFixedStartPathSum 2 N 0 k
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) i j =
      ∑ p : {p : IncreasingBlockPath N 0 // p.val 0 = i},
        if p.val.val (Fin.last 0) = j then
          realSchurGlobalWaitingSum n k B ⟨0,p.val⟩ z else 0 := by
  unfold schurFixedStartPathSum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hj : p.val.val (Fin.last 0) = j
  · simp only [hj, if_pos]
    rw [realSchurGlobalWaitingSum_eq]
    apply Finset.sum_congr rfl
    intro m hm
    exact realSchurZeroEdgeTerm_gaussian n k hk B z p.val m
  · simp only [hj, if_neg]
    simp

#print axioms realSchurZeroEdgeTerm_gaussian
#print axioms realSchurFixedStartPathSum_zero_gaussian
end SpectralRadiusUpperTail
