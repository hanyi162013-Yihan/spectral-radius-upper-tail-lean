import SpectralRadiusUpperTail.ExteriorLogDetNormalization
import SpectralRadiusUpperTail.PhaseRotationResolvent

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator

noncomputable def normalizedComplexLogDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) : ℝ := Real.log ‖(z • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det‖/(n : ℝ)

lemma phase_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (q : ℂ) (hq : ‖q‖ = 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (q⁻¹ • A)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by
  rw [map_smul, norm_smul, norm_inv, hq, inv_one, one_mul]

lemma phase_normalizedLogDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (q : ℂ) (hq : ‖q‖ = 1) (b : ℝ) :
    normalizedExteriorLogDet (q⁻¹ • A) b = normalizedComplexLogDet A (q*(b : ℂ)) := by
  have hq0 : q ≠ 0 := by intro he; simp [he] at hq
  have he : (b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-q⁻¹ • A =
      q⁻¹ • ((q*(b : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)-A) := by
    rw [smul_sub, smul_smul, inv_mul_cancel_left₀ hq0]
  unfold normalizedExteriorLogDet normalizedComplexLogDet
  rw [he, Matrix.det_smul, norm_mul, norm_pow, norm_inv, hq]
  simp

#print axioms normalizedComplexLogDet
#print axioms phase_operator_norm
#print axioms phase_normalizedLogDet
end SpectralRadiusUpperTail
