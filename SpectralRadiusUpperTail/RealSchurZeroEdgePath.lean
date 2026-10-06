import SpectralRadiusUpperTail.RealSchurPaddedPathExpansion
import SpectralRadiusUpperTail.RealSchurPaddedPowers

namespace SpectralRadiusUpperTail

/-- A path with no bridge has the true block power whenever the total
power is positive. The exponent-zero padded identity is handled separately. -/
theorem realSchurZeroEdgePath_positive {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (p : Fin 1 → Fin N) (m : Fin 1 → ℕ) (hm : 0 < m 0) :
    schurStrictPathTerm 2 N 0
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) p m =
      realSchurDataPower (B (p 0)) (m 0) (z.1 (p 0)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m 0 ≠ 0)
  simp only [schurStrictPathTerm, gaussianMatrixChain,
    realSchurPaddedDiagonal, hk]
  exact realSchurDataPower_one_pow_succ (B (p 0)) (z.1 (p 0)) k

theorem realSchurFixedStartPathSum_zero_positive {N : ℕ} (n k : ℕ)
    (hk : 0 < k) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) :
    schurFixedStartPathSum 2 N 0 k
        (realSchurPaddedDiagonal B z)
        (realSchurPaddedStrictUpper n B z) i j =
      if i = j then realSchurDataPower (B i) k (z.1 i) else 0 := by
  rw [schurFixedStartPathSum_zero]
  split_ifs
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    subst k
    exact realSchurDataPower_one_pow_succ (B i) (z.1 i) m
  · rfl

#print axioms realSchurZeroEdgePath_positive
#print axioms realSchurFixedStartPathSum_zero_positive
end SpectralRadiusUpperTail
