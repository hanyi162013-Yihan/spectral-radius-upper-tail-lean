import SpectralRadiusUpperTail.GaussianRadialBallTwo
import SpectralRadiusUpperTail.NormalizedTiltRealEvent

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma gaussian_tilt_ball_two (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = 2) (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    normalizedTilt μ (fun x => ENNReal.ofReal (Real.exp (-c*‖x‖^2))) (ball 0 R) =
      ENNReal.ofReal (1-Real.exp (-c*R^2)) := by
  have hi := gaussian_norm_integrable μ c hc
  have hz := integral_exp_pos hi
  have hnorm : 0 < μ.real (ball 0 1)/c := by
    rwa [gaussian_integral_two μ hdim c hc] at hz
  rw [normalizedTilt_ofReal_event μ _ hi (fun x => (Real.exp_pos _).le) hz _ measurableSet_ball,
    gaussian_integral_two μ hdim c hc,gaussian_integral_ball_two μ hdim c R hc hR]
  congr 1
  exact mul_div_cancel_left₀ _ hnorm.ne'

#print axioms gaussian_tilt_ball_two
end SpectralRadiusUpperTail
