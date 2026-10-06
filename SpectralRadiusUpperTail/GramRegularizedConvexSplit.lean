import SpectralRadiusUpperTail.RegularizedLogConvexDecomposition
import SpectralRadiusUpperTail.HermitianShiftDeterminant

namespace SpectralRadiusUpperTail
open scoped BigOperators ComplexOrder MatrixOrder
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

/-- The singular magnitudes are defined through the nonnegative Gram spectrum.
No ordering convention is required for the sums below. -/
noncomputable def gramSingularMagnitude (A : Matrix (Fin n) (Fin n) 𝕂) (i : Fin n) : ℝ :=
  Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)

lemma gramSingularMagnitude_sq (A : Matrix (Fin n) (Fin n) 𝕂) (i : Fin n) :
    (gramSingularMagnitude A i)^2 =
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i :=
  Real.sq_sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i)

lemma gram_regularized_logDet_convex_split (A : Matrix (Fin n) (Fin n) 𝕂)
    (τ : ℝ) (hτ : 0 < τ) :
    Real.log ‖(A.conjTranspose*A+((τ^2 : ℝ) : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det‖ =
      (n : ℝ)*(2*Real.log τ)+
        (∑ i, regularizedLogConvex₁ τ (gramSingularMagnitude A i))-
        (∑ i, regularizedLogConvex₂ τ (gramSingularMagnitude A i)) := by
  let hH := Matrix.posSemidef_conjTranspose_mul_self A
  have hd := posSemidef_shift_det_norm (A.conjTranspose*A) hH (τ^2) (sq_nonneg τ)
  rw [hd, Real.log_prod (fun i (_ : i ∈ Finset.univ) =>
    ne_of_gt (add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) (sq_pos_of_pos hτ)))]
  have he (i : Fin n) : Real.log (hH.isHermitian.eigenvalues i+τ^2) =
      2*Real.log τ+regularizedLogConvex₁ τ (gramSingularMagnitude A i)-
        regularizedLogConvex₂ τ (gramSingularMagnitude A i) := by
    rw [← gramSingularMagnitude_sq A i]
    exact regularizedLog_convex_decomposition τ _ hτ
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

lemma normalized_gram_regularized_logDet_convex_split (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) 𝕂) (τ : ℝ) (hτ : 0 < τ) :
    Real.log ‖(A.conjTranspose*A+((τ^2 : ℝ) : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det‖/(n : ℝ) =
      2*Real.log τ+
        (∑ i, regularizedLogConvex₁ τ (gramSingularMagnitude A i))/(n : ℝ)-
        (∑ i, regularizedLogConvex₂ τ (gramSingularMagnitude A i))/(n : ℝ) := by
  rw [gram_regularized_logDet_convex_split A τ hτ]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

#print axioms gramSingularMagnitude_sq
#print axioms gram_regularized_logDet_convex_split
#print axioms normalized_gram_regularized_logDet_convex_split
end SpectralRadiusUpperTail
