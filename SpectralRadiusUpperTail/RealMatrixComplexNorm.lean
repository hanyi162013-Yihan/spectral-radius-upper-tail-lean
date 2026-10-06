import SpectralRadiusUpperTail.ComplexVectorEnergy

namespace SpectralRadiusUpperTail
open WithLp
open scoped BigOperators Matrix.Norms.L2Operator

lemma real_matrix_complex_mulVec_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℂ) :
    ‖toLp 2 ((A.map Complex.ofRealHom).mulVec v)‖ ≤ ‖A‖*‖toLp 2 v‖ := by
  have hr := Matrix.l2_opNorm_mulVec A (toLp 2 (fun i => (v i).re))
  have hi := Matrix.l2_opNorm_mulVec A (toLp 2 (fun i => (v i).im))
  have hr2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have he := complex_vector_energy_split ((A.map Complex.ofRealHom).mulVec v)
  rw [real_matrix_complex_mulVec_re,real_matrix_complex_mulVec_im] at he
  have hv := complex_vector_energy_split v
  have hh : ‖toLp 2 ((A.map Complex.ofRealHom).mulVec v)‖^2 ≤ (‖A‖*‖toLp 2 v‖)^2 := by
    calc
      _ = ‖toLp 2 (A.mulVec (fun i => (v i).re))‖^2+
        ‖toLp 2 (A.mulVec (fun i => (v i).im))‖^2 := he
      _ ≤ (‖A‖*‖toLp 2 (fun i => (v i).re)‖)^2+
        (‖A‖*‖toLp 2 (fun i => (v i).im)‖)^2 := add_le_add hr2 hi2
      _ = (‖A‖*‖toLp 2 v‖)^2 := by rw [mul_pow,mul_pow,mul_pow,hv]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hh

lemma real_matrix_complex_opNorm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A.map Complex.ofRealHom)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact real_matrix_complex_mulVec_norm_le A (ofLp v)

#print axioms real_matrix_complex_mulVec_norm_le
#print axioms real_matrix_complex_opNorm_le
end SpectralRadiusUpperTail
