import SpectralRadiusUpperTail.MatrixOperatorComparison
import SpectralRadiusUpperTail.MatrixTraceMoments

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

lemma frobenius_norm_sq_trace (A : Matrix (Fin N) (Fin N) 𝕂) :
    ‖A‖^2 = RCLike.re (A*Aᴴ).trace := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rw [Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    map_sum, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]

lemma euclidean_operator_norm_sq_le_trace (A : Matrix (Fin N) (Fin N) 𝕂) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) A‖^2 ≤ RCLike.re (A*Aᴴ).trace := by
  rw [← frobenius_norm_sq_trace]
  exact pow_le_pow_left₀ (norm_nonneg _) (euclidean_operator_norm_le_frobenius A) 2

#print axioms frobenius_norm_sq_trace
#print axioms euclidean_operator_norm_sq_le_trace
end SpectralRadiusUpperTail
