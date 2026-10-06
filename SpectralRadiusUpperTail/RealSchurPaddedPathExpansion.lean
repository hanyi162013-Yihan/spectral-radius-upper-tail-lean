import SpectralRadiusUpperTail.RealSchurPaddedMatrix
import SpectralRadiusUpperTail.SchurFixedStartEqualsComponent
import SpectralRadiusUpperTail.SchurEdgeComponentSum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Diagonal blocks in the padded conditional Schur product model. -/
noncomputable def realSchurPaddedDiagonal {N : ℕ} (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i : Fin N) : Matrix (Fin 2) (Fin 2) ℝ :=
  realSchurDataPower (B i) 1 (z.1 i)

/-- Strict upper bridges in the padded conditional Schur product model. -/
noncomputable def realSchurPaddedStrictUpper {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ) :=
  Matrix.of (fun i j =>
    if i < j then realSchurPaddedBridge n B z i j else 0)

lemma realSchurPaddedStrictUpper_zero {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) (h : ¬ i < j) :
    realSchurPaddedStrictUpper n B z i j = 0 := by
  simp [realSchurPaddedStrictUpper, h]

/-- Exact diagonal-plus-strict-upper decomposition of the padded matrix. -/
theorem realSchurPaddedMatrix_decompose {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    realSchurPaddedMatrix n B z =
      Matrix.diagonal (realSchurPaddedDiagonal B z) +
        realSchurPaddedStrictUpper n B z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [realSchurPaddedMatrix, realSchurPaddedDiagonal,
      realSchurPaddedStrictUpper]
  · by_cases hlt : i < j
    · simp [realSchurPaddedMatrix, realSchurPaddedDiagonal,
        realSchurPaddedStrictUpper, hij, hlt]
    · simp [realSchurPaddedMatrix, realSchurPaddedDiagonal,
        realSchurPaddedStrictUpper, hij, hlt]

/-- Every block of every power of the actual padded Schur product-model
matrix is the explicit sum over strict block paths and waiting times. -/
theorem realSchurPaddedPower_strict_path_sum {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) :
    ((realSchurPaddedMatrix n B z)^k) i j =
      ∑ l ∈ Finset.range (k+1),
        schurFixedStartPathSum 2 N l k
          (realSchurPaddedDiagonal B z)
          (realSchurPaddedStrictUpper n B z) i j := by
  let D := realSchurPaddedDiagonal B z
  let U := realSchurPaddedStrictUpper n B z
  have hU : ∀ a b : Fin N, ¬ a < b → U a b = 0 := by
    intro a b h
    exact realSchurPaddedStrictUpper_zero n B z a b h
  have hdec : realSchurPaddedMatrix n B z = Matrix.diagonal D + U :=
    realSchurPaddedMatrix_decompose n B z
  have hsum := noncomm_edge_component_sum (Matrix.diagonal D) U k
  calc
    ((realSchurPaddedMatrix n B z)^k) i j =
        (∑ l ∈ Finset.range (k+1),
          noncommEdgeComponent (Matrix.diagonal D) U l k) i j := by
      rw [hsum, ← hdec]
    _ = ∑ l ∈ Finset.range (k+1),
          (noncommEdgeComponent (Matrix.diagonal D) U l k) i j := by
      rw [Matrix.sum_apply]
    _ = ∑ l ∈ Finset.range (k+1),
          schurFixedStartPathSum 2 N l k D U i j := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
      exact (schurFixedStartPathSum_eq_component 2 N D U hU l k hlk i j).symm

#print axioms realSchurPaddedMatrix_decompose
#print axioms realSchurPaddedPower_strict_path_sum
end SpectralRadiusUpperTail
