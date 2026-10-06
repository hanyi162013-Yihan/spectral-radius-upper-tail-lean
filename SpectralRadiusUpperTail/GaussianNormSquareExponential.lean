import SpectralRadiusUpperTail.GaussianTiltBallTwo
import SpectralRadiusUpperTail.ExponentialFirstMoment
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma gaussian_tilt_closedBall_two (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = 2) (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    normalizedTilt μ (fun x => ENNReal.ofReal (Real.exp (-c*‖x‖^2))) (closedBall 0 R) =
      ENNReal.ofReal (1-Real.exp (-c*R^2)) := by
  have hz : normalizedTilt μ (fun x => ENNReal.ofReal (Real.exp (-c*‖x‖^2))) (sphere 0 R) = 0 :=
    withDensity_absolutelyContinuous μ _ (Measure.addHaar_sphere μ 0 R)
  rw [← ball_union_sphere,measure_union sphere_disjoint_ball.symm isClosed_sphere.measurableSet,
    hz,add_zero,gaussian_tilt_ball_two μ hdim c R hc hR]

/-- In two real dimensions, squared radius under an isotropic Gaussian tilt is exponential. -/
lemma gaussian_normSquare_exponential (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = 2) (c : ℝ) (hc : 0 < c) :
    (normalizedTilt μ (fun x => ENNReal.ofReal (Real.exp (-c*‖x‖^2)))).map
      (fun x => ‖x‖^2) = expMeasure c := by
  let P := normalizedTilt μ (fun x => ENNReal.ofReal (Real.exp (-c*‖x‖^2)))
  have hz := gaussian_norm_normalizer_bounds μ c hc
  letI : IsProbabilityMeasure P := normalizedTilt_probability μ _ hz.1 hz.2
  change P.map (fun x => ‖x‖^2) = expMeasure c
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,expMeasure_eq_density,
    withDensity_apply _ measurableSet_Iic,lintegral_exponentialPDF_eq_antiDeriv hc]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    have he : (fun x : E => ‖x‖^2) ⁻¹' Set.Iic t = closedBall 0 (Real.sqrt t) := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Iic,mem_closedBall,dist_zero_right]
      exact (Real.le_sqrt (norm_nonneg x) ht).symm
    rw [he]
    change normalizedTilt μ _ (closedBall 0 (Real.sqrt t)) = _
    rw [gaussian_tilt_closedBall_two μ hdim c (Real.sqrt t) hc (Real.sqrt_nonneg t),
      Real.sq_sqrt ht]
    simp only [neg_mul]
  · rw [if_neg ht]
    have he : (fun x : E => ‖x‖^2) ⁻¹' Set.Iic t = ∅ := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_empty_iff_false,iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge ht) (sq_nonneg ‖x‖))
    rw [he,measure_empty,ENNReal.ofReal_zero]

#print axioms gaussian_tilt_closedBall_two
#print axioms gaussian_normSquare_exponential
end SpectralRadiusUpperTail
