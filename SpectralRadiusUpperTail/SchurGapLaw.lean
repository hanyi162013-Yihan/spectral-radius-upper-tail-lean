import SpectralRadiusUpperTail.SchurGapWeight
import SpectralRadiusUpperTail.NormalizedTiltIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Explicit squared-gap law in the real Schur density calculation.
Identifying this law with a Gaussian matrix's conditional Schur law is
not asserted by this definition. -/
noncomputable def schurSquaredGapLaw (n y : ℝ) : Measure ℝ :=
  normalizedTilt (expMeasure (n/2)) (fun s => ENNReal.ofReal (schurGapWeight y s))

lemma schurGapWeight_measurable (y : ℝ) : Measurable (schurGapWeight y) := by
  unfold schurGapWeight
  fun_prop

lemma schurGapWeight_normalizer_pos (n y : ℝ) (hn : 0 < n) (hy : 0 < y) :
    0 < ∫ s : ℝ, schurGapWeight y s ∂expMeasure (n/2) := by
  have hn2 : 0 < n/2 := by positivity
  haveI := isProbabilityMeasure_expMeasure hn2
  apply (integral_pos_iff_support_of_nonneg
    (fun s => (schurGapWeight_positive y hy s).le)
    (schurGapWeight_integrable _ y hy)).mpr
  have hs : Function.support (schurGapWeight y) = Set.univ := by
    ext s
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (schurGapWeight_positive y hy s).ne'
  rw [hs]
  simp

lemma schurSquaredGapLaw_probability (n y : ℝ) (hn : 0 < n) (hy : 0 < y) :
    IsProbabilityMeasure (schurSquaredGapLaw n y) := by
  haveI := isProbabilityMeasure_expMeasure (show 0 < n/2 by positivity)
  exact normalizedTilt_ofReal_probability _ _ (schurGapWeight_integrable _ y hy)
    (fun s => (schurGapWeight_positive y hy s).le)
    (schurGapWeight_normalizer_pos n y hn hy)

lemma schurSquaredGapLaw_nonnegative (n y : ℝ) (hn : 0 < n) :
    ∀ᵐ s ∂schurSquaredGapLaw n y, 0 ≤ s := by
  exact (Measure.ae_le_iff_absolutelyContinuous.mpr (withDensity_absolutelyContinuous _ _))
    (exponential_nonnegative_ae (n/2) (by positivity))

lemma schurSquaredGapLaw_integrable (n y : ℝ) (hn : 0 < n) (hy : 0 < y) :
    Integrable (fun s : ℝ => s) (schurSquaredGapLaw n y) := by
  haveI := isProbabilityMeasure_expMeasure (show 0 < n/2 by positivity)
  apply integrable_normalizedTilt_ofReal _ _ _ (schurGapWeight_integrable _ y hy)
    (schurGapWeight_measurable y) (fun s => (schurGapWeight_positive y hy s).le)
    (schurGapWeight_normalizer_pos n y hn hy)
  simpa only [mul_comm] using schurGapWeight_id_integrable (expMeasure (n/2))
    (exponential_first_moment (n/2) (by positivity)).1 y hy

/-- Uniform mean of the squared gap under the fully normalized law. -/
theorem schurSquaredGapLaw_mean_le (n y : ℝ) (hn : 0 < n) (hy : 0 < y) :
    (∫ s : ℝ, s ∂schurSquaredGapLaw n y) ≤ 2/n := by
  haveI := isProbabilityMeasure_expMeasure (show 0 < n/2 by positivity)
  rw [schurSquaredGapLaw, integral_normalizedTilt_ofReal _ _ _
    (schurGapWeight_integrable _ y hy) (schurGapWeight_measurable y)
    (fun s => (schurGapWeight_positive y hy s).le)
    (schurGapWeight_normalizer_pos n y hn hy)]
  simpa only [mul_comm] using schur_gap_weighted_second_moment n y hn hy

#print axioms schurSquaredGapLaw_probability
#print axioms schurSquaredGapLaw_integrable
#print axioms schurSquaredGapLaw_mean_le
end SpectralRadiusUpperTail
