import SpectralRadiusUpperTail.TiltEventPositive
import SpectralRadiusUpperTail.RealMatrixTiltOutlier
import SpectralRadiusUpperTail.FlatHaarPrior

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Positivity of the original upper-tail event follows from the constructed
outlier tilt, without any bulk-concentration assumption. -/
lemma real_spectral_tail_eventually_positive
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (r : ℝ) (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop,
      0 < (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} := by
  let ν : (n : ℕ) → Measure (flatUnitDirections ℝ n 2) :=
    fun n => haarFlatPrior ℝ n 2 (by norm_num)
  letI : ∀ n, IsProbabilityMeasure (ν n) :=
    fun n => haarFlatPrior_probability ℝ n 2 (by norm_num)
  let b : ℝ := 2*(r+1)
  have hb : r < ‖((b/(1+1) : ℝ) : ℂ)‖ := by
    have he : b/(1+1) = r+1 := by dsimp [b]; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r+1)]
    linarith
  letI : ∀ n, IsProbabilityMeasure (flatSpectralMatrixTilt μ (ν n) (2*1) b) :=
    fun n => flatSpectralMatrixTilt_probability μ (ν n) (2*1) (by norm_num) b
  apply original_event_eventually_positive (fun n => Fin n → Fin n → ℝ)
    (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (fun n => flatSpectralMatrixTilt μ (ν n) (2*1) b)
    (fun n => withDensity_absolutelyContinuous _ _) _
    (fun n => measurableSet_lt measurable_const
      (complex_spectralRadius_measurable.comp
        ((continuous_id.matrix_map Complex.continuous_ofReal).measurable.comp
          measurable_normalizedArray)).ennreal_toReal)
  simpa only [Set.compl_setOf, not_lt, Function.comp_apply, id_eq] using!
    real_matrix_spectralTilt_radius_probability μ hm hv c hc hexp
      1 2 (by norm_num) (by norm_num) ν b r hr hb

#print axioms real_spectral_tail_eventually_positive
end SpectralRadiusUpperTail
