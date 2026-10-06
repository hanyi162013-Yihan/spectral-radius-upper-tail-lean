import SpectralRadiusUpperTail.RealSchurPaddedMatrix
import SpectralRadiusUpperTail.SchurBlockDuhamel

namespace SpectralRadiusUpperTail
open scoped BigOperators

noncomputable def realSchurPaddedUpper {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ) :=
  Matrix.of (fun i j => if i < j then realSchurPaddedBridge n B z i j else 0)

lemma realSchurPaddedMatrix_diagonal_add_upper {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    realSchurPaddedMatrix n B z =
      Matrix.diagonal (fun i => realSchurDataPower (B i) 1 (z.1 i)) +
        realSchurPaddedUpper n B z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [realSchurPaddedMatrix, realSchurPaddedUpper]
  · by_cases hlt : i < j
    · simp [realSchurPaddedMatrix, realSchurPaddedUpper, hij, hlt]
    · simp [realSchurPaddedMatrix, realSchurPaddedUpper, hij, hlt]

/-- Recursive entry formula for the padded real Schur power. This is the
algebraic entry point for grouping monotone walks by first strict edge. -/
theorem real_schur_padded_power_duhamel {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) (i j : Fin N) :
    ((realSchurPaddedMatrix n B z)^k) i j =
      (if i = j then (realSchurDataPower (B i) 1 (z.1 i))^k else 0) +
      ∑ s ∈ Finset.range k, ∑ h : Fin N,
        (realSchurDataPower (B i) 1 (z.1 i))^s *
          (realSchurPaddedUpper n B z) i h *
          ((realSchurPaddedMatrix n B z)^(k-s-1)) h j := by
  rw [realSchurPaddedMatrix_diagonal_add_upper]
  exact diagonal_plus_upper_power_entry _ _ k i j

#print axioms realSchurPaddedMatrix_diagonal_add_upper
#print axioms real_schur_padded_power_duhamel
end SpectralRadiusUpperTail
