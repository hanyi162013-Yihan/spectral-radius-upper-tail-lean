import SpectralRadiusUpperTail.RealSharpClassUnconditional
import SpectralRadiusUpperTail.RealGaussianRadiusLawBridge

namespace SpectralRadiusUpperTail
open MeasureTheory Filter ProbabilityTheory
open scoped Topology

theorem standardNormal_symmetric_proved : standardNormal.map (fun x : ℝ => -x)=standardNormal := by
  simp [standardNormal, gaussianReal_map_neg]

/-- Sharp real Gaussian radius tails for the actual normalized iid array.
All Gaussian and concentration inputs are proved in the project. -/
theorem realGaussian_radius_two_sided_proved
    (r : ℝ) (hr : 1 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate 1 r-ε)) ≤
        (gaussianMatrixLaw n).real
          {a | r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)} ∧
      (gaussianMatrixLaw n).real
          {a | r ≤ realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)} ≤
        Real.exp ((n : ℝ)*(-rate 1 r+ε)) := by
  simpa only [realGaussian_radius_strict_tail_eq_nested,
    realGaussian_radius_closed_tail_eq_nested] using
    real_class_sharp_two_sided_of_entry_hypotheses standardNormal
      standardNormal_symmetric_proved standardNormal_second_moment
      standardNormal_gaussian_even_domination r hr ε hε

theorem realGaussian_radius_log_tail_limits_proved (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n => Real.log ((gaussianMatrixLaw n).real
      {a | r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)})/(n : ℝ))
        atTop (𝓝 (-rate 1 r)) ∧
    Tendsto (fun n => Real.log ((gaussianMatrixLaw n).real
      {a | r ≤ realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)})/(n : ℝ))
        atTop (𝓝 (-rate 1 r)) := by
  simpa only [realGaussian_radius_strict_tail_eq_nested,
    realGaussian_radius_closed_tail_eq_nested] using
    real_class_sharp_log_tail_limits_of_entry_hypotheses standardNormal
      standardNormal_symmetric_proved standardNormal_second_moment
      standardNormal_gaussian_even_domination r hr

/-- Full open/closed set bounds for max(1,radius), with speed n and
rate I₁, for the actual normalized real iid Gaussian matrix. -/
theorem realGaussian_clipped_radius_LDP_proved :
    ClippedDeviationBounds (fun n => Fin n × Fin n → ℝ) gaussianMatrixLaw
      (fun n a => realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix a)) 1 := by
  apply clipped_deviation_bounds_of_tails _ _ _ 1 (by norm_num)
  exact realGaussian_radius_two_sided_proved

#print axioms standardNormal_symmetric_proved
#print axioms realGaussian_radius_two_sided_proved
#print axioms realGaussian_radius_log_tail_limits_proved
#print axioms realGaussian_clipped_radius_LDP_proved
end SpectralRadiusUpperTail
