import SpectralRadiusUpperTail.RealSchurBlockSupport
import SpectralRadiusUpperTail.RealSchurGlobalModel
import SpectralRadiusUpperTail.SchurBlockPowerWalk

namespace SpectralRadiusUpperTail
open scoped Matrix
open Classical

/-- A full `2 × 2` Gaussian bridge restricted to the active coordinates of
the actual one- or two-dimensional Schur blocks. -/
noncomputable def realSchurPaddedBridge {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) (i j : Fin N) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  realSchurDataPower (B i) 0 (z.1 i) *
    ((1/Real.sqrt n) • Matrix.of (fun a b => z.2 ((i,j),(a,b)))) *
    realSchurDataPower (B j) 0 (z.1 j)

lemma realSchurPaddedBridge_left_support {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) (i j : Fin N) :
    realSchurDataPower (B i) 0 (z.1 i) * realSchurPaddedBridge n B z i j =
      realSchurPaddedBridge n B z i j := by
  unfold realSchurPaddedBridge
  simp only [← mul_assoc, realSchurDataPower_zero_idempotent]

lemma realSchurPaddedBridge_right_support {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) (i j : Fin N) :
    realSchurPaddedBridge n B z i j * realSchurDataPower (B j) 0 (z.1 j) =
      realSchurPaddedBridge n B z i j := by
  unfold realSchurPaddedBridge
  rw [mul_assoc, realSchurDataPower_zero_idempotent]

/-- The block matrix of the explicit conditional Schur product model. -/
noncomputable def realSchurPaddedMatrix {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ) :=
  Matrix.of (fun i j =>
    if i = j then realSchurDataPower (B i) 1 (z.1 i)
    else if i < j then realSchurPaddedBridge n B z i j else 0)

lemma realSchurPaddedMatrix_upper {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) (h : j < i) : realSchurPaddedMatrix n B z i j = 0 := by
  simp [realSchurPaddedMatrix, ne_of_gt h, not_lt_of_ge (le_of_lt h)]

lemma realSchurPaddedMatrix_left_support {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) (i j : Fin N) :
    realSchurDataPower (B i) 0 (z.1 i) * realSchurPaddedMatrix n B z i j =
      realSchurPaddedMatrix n B z i j := by
  by_cases hij : i = j
  · subst j
    simp [realSchurPaddedMatrix, realSchurDataPower_zero_left]
  · by_cases hlt : i < j
    · simp [realSchurPaddedMatrix, hij, hlt, realSchurPaddedBridge_left_support]
    · simp [realSchurPaddedMatrix, hij, hlt]

lemma realSchurPaddedMatrix_right_support {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) (i j : Fin N) :
    realSchurPaddedMatrix n B z i j * realSchurDataPower (B j) 0 (z.1 j) =
      realSchurPaddedMatrix n B z i j := by
  by_cases hij : i = j
  · subst j
    simp [realSchurPaddedMatrix, realSchurDataPower_zero_right]
  · by_cases hlt : i < j
    · simp [realSchurPaddedMatrix, hij, hlt, realSchurPaddedBridge_right_support]
    · simp [realSchurPaddedMatrix, hij, hlt]

/-- The actual matrix power has no downward block walks. -/
theorem real_schur_padded_power_weak_walk_sum {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) (i j : Fin N) :
    ((realSchurPaddedMatrix n B z)^k) i j =
      ∑ v : Fin k → Fin N,
        if blockWalkWeakIncreasing k i j v then
          blockPowerWalk (realSchurPaddedMatrix n B z) k i j v else 0 := by
  exact upper_block_power_weak_walk_sum _
    (realSchurPaddedMatrix_upper n B z) k i j

#print axioms realSchurPaddedMatrix_upper
#print axioms real_schur_padded_power_weak_walk_sum
end SpectralRadiusUpperTail
