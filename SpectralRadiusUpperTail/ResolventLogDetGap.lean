import SpectralRadiusUpperTail.GramLogDetRegularizationGap
import SpectralRadiusUpperTail.MatrixRegularizedLogDet

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator

lemma matrix_resolvent_negative_left_inverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : z ∈ resolventSet ℂ A) :
    ∀ v : EuclideanSpace ℂ (Fin n),
      (-Matrix.toEuclideanCLM (𝕜 := ℂ) (resolvent A z))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (A-z • 1) v) = v := by
  have hi : resolvent A z*(z • (1 : Matrix (Fin n) (Fin n) ℂ)-A) = 1 := by
    simpa only [resolvent, Algebra.algebraMap_eq_smul_one] using!
      Ring.inverse_mul_cancel _ (spectrum.mem_resolventSet_iff.mp hz)
  have he : (-resolvent A z)*(A-z • 1) = 1 := by
    rw [show A-z • 1 = -(z • 1-A) by abel, neg_mul_neg, hi]
  intro v
  have hh := congrArg (fun B => Matrix.toEuclideanCLM (𝕜 := ℂ) B v) he
  simpa only [map_mul, map_neg, map_one, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_apply] using hh

lemma matrixRegularizedLogDet_le_exterior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (b s M : ℝ) (hs : 0 ≤ s) (hM : 0 < M)
    (hb : (b : ℂ) ∈ resolventSet ℂ A)
    (hR : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (resolvent A (b : ℂ))‖ ≤ M) :
    matrixRegularizedLogDet A b s ≤
      2*Real.log ‖((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det‖+(n : ℝ)*s*M^2 := by
  have hh := gram_logDet_regularization_gap (A-(b : ℂ) • 1)
    (-Matrix.toEuclideanCLM (𝕜 := ℂ) (resolvent A (b : ℂ)))
    (matrix_resolvent_negative_left_inverse A b hb) M s hM
    (by simpa only [norm_neg] using hR) hs
  rw [matrix_gram_det_norm, matrix_shift_det_norm_sub_comm, Real.log_pow] at hh
  change matrixRegularizedLogDet A b s-_ ≤ _ at hh
  convert! (sub_le_iff_le_add).mp hh using 1 <;> ring

#print axioms matrix_resolvent_negative_left_inverse
#print axioms matrixRegularizedLogDet_le_exterior
end SpectralRadiusUpperTail
