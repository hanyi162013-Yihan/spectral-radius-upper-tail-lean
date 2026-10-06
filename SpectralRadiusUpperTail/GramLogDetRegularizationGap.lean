import SpectralRadiusUpperTail.GramEigenvalueLower
import SpectralRadiusUpperTail.PositiveShiftLogGap
import SpectralRadiusUpperTail.HermitianShiftDeterminant

namespace SpectralRadiusUpperTail
open scoped BigOperators ComplexOrder MatrixOrder

lemma gram_logDet_regularization_gap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hSA : ∀ v, S (Matrix.toEuclideanCLM (𝕜 := ℂ) A v) = v)
    (M s : ℝ) (hM : 0 < M) (hS : ‖S‖ ≤ M) (hs : 0 ≤ s) :
    Real.log ‖(A.conjTranspose*A+(s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖-
      Real.log ‖(A.conjTranspose*A).det‖ ≤ (n : ℝ)*s*M^2 := by
  let hH := Matrix.posSemidef_conjTranspose_mul_self A
  have he : ‖(A.conjTranspose*A).det‖ = ∏ i, hH.isHermitian.eigenvalues i := by
    simpa only [RCLike.ofReal_zero, zero_smul, add_zero] using!
      posSemidef_shift_det_norm (A.conjTranspose*A) hH 0 le_rfl
  have hsdet : ‖(A.conjTranspose*A+(s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖ =
      ∏ i, (hH.isHermitian.eigenvalues i+s) := by
    convert! posSemidef_shift_det_norm (A.conjTranspose*A) hH s hs using 1
  rw [hsdet, he]
  simpa only [Fintype.card_fin] using log_product_positive_shift_gap
    hH.isHermitian.eigenvalues s (M^2)
    (fun i => (gram_eigenvalues_inverse_bound A S hSA M hM hS i).1) hs
    (fun i => (gram_eigenvalues_inverse_bound A S hSA M hM hS i).2)

#print axioms gram_logDet_regularization_gap
end SpectralRadiusUpperTail
