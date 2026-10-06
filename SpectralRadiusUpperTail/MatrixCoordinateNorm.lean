import SpectralRadiusUpperTail.MatrixCoordinateMap
import SpectralRadiusUpperTail.MatrixOperatorComparison
import SpectralRadiusUpperTail.TriangularNorm

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

/-- A single actual matrix coordinate has Frobenius norm equal to the scalar
norm; this gives a dimension-free Euclidean operator bound for one increment. -/
lemma matrixCoordinate_frobenius_norm (i j : Fin N) (z : 𝕂) :
    ‖(matrixCoordinateL i j z : Matrix (Fin N) (Fin N) 𝕂)‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq_eq_sum]
  have he (p q : Fin N) : ‖matrixCoordinateL i j z p q‖^2 =
      if p=i then if q=j then ‖z‖^2 else 0 else 0 := by
    rw [matrixCoordinateL_apply]
    by_cases hp : p=i <;> by_cases hq : q=j <;> simp [hp,hq]
  simp only [he]
  simp

lemma matrixCoordinate_scaled_operator_le (i j : Fin N) (z : 𝕂) (c : ℝ) (hc : 0 ≤ c) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
      (c • (matrixCoordinateL i j z : Matrix (Fin N) (Fin N) 𝕂))‖ ≤ c*‖z‖ := by
  apply (euclidean_operator_norm_le_frobenius _).trans_eq
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, matrixCoordinate_frobenius_norm]

#print axioms matrixCoordinate_scaled_operator_le
end SpectralRadiusUpperTail
