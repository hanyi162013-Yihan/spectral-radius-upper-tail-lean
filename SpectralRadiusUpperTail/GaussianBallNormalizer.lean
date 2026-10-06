import SpectralRadiusUpperTail.GaussianNormIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma gaussian_ball_normalizer_ratio (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∫⁻ x : E, ENNReal.ofReal (Real.exp (-‖x‖^2)) ∂μ)/μ (ball 0 1) =
      ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ E : ℝ)/2+1)) := by
  have hG : 0 < Real.Gamma ((Module.finrank ℝ E : ℝ)/2+1) := Real.Gamma_pos_of_pos (by positivity)
  have hG0 : ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ E : ℝ)/2+1)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hG)
  have hV0 : μ (ball (0 : E) 1) ≠ 0 := isOpen_ball.measure_ne_zero μ (nonempty_ball.mpr zero_lt_one)
  have hVtop : μ (ball (0 : E) 1) ≠ ∞ := ne_of_lt measure_ball_lt_top
  have hi : Integrable (fun x : E => Real.exp (-‖x‖^2)) μ := by
    simpa using gaussian_norm_integrable μ 1 (by norm_num)
  have he := measure_unitBall_eq_integral_div_gamma μ (by norm_num : (0 : ℝ) < 2)
  have hz := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x : E => (Real.exp_pos (-‖x‖^2)).le))
  simp only [Real.rpow_two,ENNReal.ofReal_div_of_pos hG] at he
  rw [hz] at he
  symm
  apply (ENNReal.eq_div_iff hV0 hVtop).mpr
  simpa only [mul_comm] using (ENNReal.eq_div_iff hG0 ENNReal.ofReal_ne_top).mp he

#print axioms gaussian_ball_normalizer_ratio
end SpectralRadiusUpperTail
