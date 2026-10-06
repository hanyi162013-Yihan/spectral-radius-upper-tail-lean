import SpectralRadiusUpperTail.TiltEventPositive
import SpectralRadiusUpperTail.ComplexMatrixTiltOutlier
import SpectralRadiusUpperTail.FlatHaarPrior

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Positivity of the original upper-tail event follows from the constructed
outlier tilt, without any bulk-concentration assumption. -/
lemma complex_spectral_tail_eventually_positive
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (r : ℝ) (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop,
      0 < (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal} := by
  let ν : (n : ℕ) → Measure (flatUnitDirections ℂ n 2) :=
    fun n => haarFlatPrior ℂ n 2 (by norm_num)
  letI : ∀ n, IsProbabilityMeasure (ν n) :=
    fun n => haarFlatPrior_probability ℂ n 2 (by norm_num)
  let b : ℂ := (2*(r+1) : ℝ)
  have hb : r < ‖b/((1+1 : ℝ) : ℂ)‖ := by
    have he : b/((1+1 : ℝ) : ℂ) = ((r+1 : ℝ) : ℂ) := by
      dsimp [b]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r+1)]
    linarith
  letI : ∀ n, IsProbabilityMeasure (flatSpectralMatrixTilt μ (ν n) 1 b) :=
    fun n => flatSpectralMatrixTilt_probability μ (ν n) 1 (by norm_num) b
  apply original_event_eventually_positive (fun n => Fin n → Fin n → ℂ)
    (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (fun n => flatSpectralMatrixTilt μ (ν n) 1 b)
    (fun n => withDensity_absolutelyContinuous _ _) _
    (fun n => measurableSet_lt measurable_const
      (complex_spectralRadius_measurable.comp measurable_normalizedArray).ennreal_toReal)
  simpa only [Set.compl_setOf, not_lt, Function.comp_apply] using!
    complex_matrix_spectralTilt_radius_probability μ hm hv hp c hc hexp
      1 2 (by norm_num) (by norm_num) ν b r hr hb

#print axioms complex_spectral_tail_eventually_positive
end SpectralRadiusUpperTail
