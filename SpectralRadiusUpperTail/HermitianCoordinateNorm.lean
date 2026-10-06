import SpectralRadiusUpperTail.DiagonalVarianceMap
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace SpectralRadiusUpperTail
open Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

lemma dilationVarianceCoordinateL_operator_le (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
      (dilationVarianceCoordinateL (𝕂 := 𝕂) i j r)‖ ≤ r := by
  have he : dilationVarianceCoordinateL (𝕂 := 𝕂) i j r = Matrix.diagonal
      (fun p : Fin N ⊕ Fin N => match p with
        | Sum.inl k => if k=i then (r : 𝕂) else 0
        | Sum.inr k => if k=j then (r : 𝕂) else 0) := by
    ext p q
    rw [dilationVarianceCoordinateL_apply, Matrix.diagonal_apply]
    rfl
  rw [he, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro p
  cases p <;> dsimp only <;> split_ifs <;> simp [RCLike.norm_ofReal, abs_of_nonneg hr, hr]

/-- Dilation of one coordinate has the same scalar operator bound; no
Frobenius dimension factor or extra sqrt(2) constant is introduced. -/
theorem hermitian_matrixCoordinate_operator_le (i j : Fin N) (z : 𝕂) :
    ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
      (hermitianDilation (matrixCoordinateL i j z))‖ ≤ ‖z‖ := by
  let H := hermitianDilation (matrixCoordinateL i j z)
  let T := Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
  have hs : star H = H := hermitianDilation_isHermitian _
  have ht : star (T H) = T H := by rw [← map_star, hs]
  have he : ‖T H‖^2 = ‖T (H*H)‖ := by
    calc
      _ = ‖star (T H)*(T H)‖ := by
        simpa only [pow_two] using (CStarRing.norm_star_mul_self (x := T H)).symm
      _ = _ := by rw [map_mul, ht]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [he]
  have hsq : H*H = dilationVarianceCoordinateL (𝕂 := 𝕂) i j (‖z‖^2) := by
    rw [dilationVarianceCoordinateL_blocks]
    exact matrixCoordinate_dilation_square i j z
  rw [hsq]
  exact dilationVarianceCoordinateL_operator_le i j (‖z‖^2) (sq_nonneg _)

lemma hermitian_scaled_matrixCoordinate_operator_le (i j : Fin N) (z : 𝕂)
    (c : ℝ) (hc : 0 ≤ c) :
    ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂)
      (hermitianDilation (c • matrixCoordinateL i j z))‖ ≤ c*‖z‖ := by
  rw [← map_smul]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] using
    hermitian_matrixCoordinate_operator_le i j (c • z)

#print axioms hermitian_scaled_matrixCoordinate_operator_le
end SpectralRadiusUpperTail
