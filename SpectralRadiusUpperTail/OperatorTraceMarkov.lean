import SpectralRadiusUpperTail.OperatorDyadicTraceBound

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {Ω 𝕂 : Type*} [MeasurableSpace Ω] [RCLike 𝕂] {N : ℕ}

lemma operator_probability_le_dyadic_trace (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Ω → Matrix (Fin N) (Fin N) 𝕂) (k : ℕ)
    (hi : Integrable (fun x => matrixTraceMoment (2^(k+1)) (A x)) μ)
    (R : ℝ) (hR : 0 < R) :
    μ.real {x | R ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) (A x)‖} ≤
      (∫ x, matrixTraceMoment (2^(k+1)) (A x) ∂μ)/R^(2*(2^(k+1))) := by
  have hsub : {x | R ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) (A x)‖} ⊆
      {x | R^(2*(2^(k+1))) ≤ matrixTraceMoment (2^(k+1)) (A x)} := by
    intro x hx
    exact (pow_le_pow_left₀ hR.le hx _).trans (operator_norm_dyadic_le_trace (A x) k)
  have hh := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => matrixTraceMoment_nonneg _ (A x))) hi
      (R^(2*(2^(k+1))))
  have hp := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsub)
    (pow_nonneg hR.le _)).trans hh
  exact (le_div_iff₀ (pow_pos hR _)).mpr (by simpa only [mul_comm] using hp)

#print axioms operator_probability_le_dyadic_trace
end SpectralRadiusUpperTail
