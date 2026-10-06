import SpectralRadiusUpperTail.MatrixCoefficient

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

/-- The normalized trace, defined also in dimension zero. -/
noncomputable def normalizedMatrixTrace (A : Matrix (Fin n) (Fin n) 𝕂) : 𝕂 :=
  (n : 𝕂)⁻¹ * Matrix.trace A

lemma coordinateVector_energy (i : Fin n) :
    (∑ j, ‖(Pi.single i (1 : 𝕂) : Fin n → 𝕂) j‖^2) = 1 := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · simp

lemma matrixCoefficient_coordinate (i : Fin n) (A : Matrix (Fin n) (Fin n) 𝕂) :
    matrixCoefficient (Pi.single i 1) (Pi.single i 1) A = A i i := by
  classical
  simp [matrixCoefficient_eq_sum, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma matrix_diagonal_norm_le (A : Matrix (Fin n) (Fin n) 𝕂) (i : Fin n) :
    ‖A i i‖ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A‖ := by
  rw [← matrixCoefficient_coordinate i A]
  exact matrixCoefficient_norm_le _ _ (coordinateVector_energy i).le
    (coordinateVector_energy i).le A

lemma normalizedMatrixTrace_norm_le (A : Matrix (Fin n) (Fin n) 𝕂) :
    ‖normalizedMatrixTrace A‖ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A‖ := by
  by_cases hn : n = 0
  · subst n
    simp [normalizedMatrixTrace]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs : ‖Matrix.trace A‖ ≤ (n : ℝ) *
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A‖ := by
    apply (norm_sum_le _ _).trans
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => matrix_diagonal_norm_le A i)
  rw [normalizedMatrixTrace, norm_mul, norm_inv, RCLike.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A‖) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp

lemma normalizedMatrixTrace_one (hn : 0 < n) :
    normalizedMatrixTrace (1 : Matrix (Fin n) (Fin n) 𝕂) = 1 := by
  simp [normalizedMatrixTrace, Matrix.trace_one, Nat.ne_of_gt hn]

lemma normalizedMatrixTrace_add (A B : Matrix (Fin n) (Fin n) 𝕂) :
    normalizedMatrixTrace (A+B) = normalizedMatrixTrace A + normalizedMatrixTrace B := by
  simp [normalizedMatrixTrace, Matrix.trace_add, mul_add]

lemma normalizedMatrixTrace_smul (s : 𝕂) (A : Matrix (Fin n) (Fin n) 𝕂) :
    normalizedMatrixTrace (s • A) = s * normalizedMatrixTrace A := by
  simp [normalizedMatrixTrace, Matrix.trace_smul, mul_left_comm]

#print axioms normalizedMatrixTrace
#print axioms coordinateVector_energy
#print axioms matrixCoefficient_coordinate
#print axioms matrix_diagonal_norm_le
#print axioms normalizedMatrixTrace_norm_le
#print axioms normalizedMatrixTrace_one
#print axioms normalizedMatrixTrace_add
#print axioms normalizedMatrixTrace_smul
end SpectralRadiusUpperTail
