import SpectralRadiusUpperTail.ReversedMatrix
import SpectralRadiusUpperTail.MatrixOperatorComparison
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

/-- A dimension-independent bound for the actual triangular operator. -/
lemma descendingTriangularInverse_operator_bound (η : ℝ) (hη : 0 < η)
    (v : Fin N → 𝕂) (hv : ∑ i, ‖v i‖^2 = 1) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) (descendingTriangularInverse η v)‖ ≤
      1+Real.sqrt (1/(2*η^2)) := by
  let A := descendingTriangularInverse η v
  let T := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂)
  have hf : ‖A-1‖ ≤ Real.sqrt (1/(2*η^2)) := by
    have hh := descendingTriangularInverse_norm_sq_le η hη v hv
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 1/(2*η^2))
    have hp := Real.sqrt_nonneg (1/(2*η^2))
    change ‖A-1‖^2 ≤ _ at hh
    nlinarith [norm_nonneg (A-1)]
  have ho := (euclidean_operator_norm_le_frobenius (A-1)).trans hf
  have h1 : ‖T 1‖ ≤ 1 := by
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  have hh := norm_add_le (T (A-1)) (T 1)
  rw [← map_add, sub_add_cancel] at hh
  change ‖T A‖ ≤ _
  linarith

#print axioms descendingTriangularInverse_operator_bound
end SpectralRadiusUpperTail
