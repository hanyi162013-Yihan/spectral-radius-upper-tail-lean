import SpectralRadiusUpperTail.ComplexLocalEvent
import SpectralRadiusUpperTail.ComplexMatrixTiltOutlier
import SpectralRadiusUpperTail.TiltEventPositive

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology ENNReal

lemma complex_matrix_spectralTilt_local_probability
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (u L : ℝ) (hu : 0 < u) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℂ) (hb : 1 < ‖b/((u+1 : ℝ) : ℂ)‖) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) u b).real
      (complexLocalEigenvalueEvent n (b/((u+1 : ℝ) : ℂ)) δ)ᶜ) atTop (𝓝 0) := by
  let d := min δ (‖b/((u+1 : ℝ) : ℂ)‖-1)/4
  have hd : 0 < d := div_pos (lt_min hδ (by linarith)) (by norm_num)
  have hdδ : d < δ := by
    have hh := min_le_left δ (‖b/((u+1 : ℝ) : ℂ)‖-1)
    dsimp [d]
    linarith
  have hgap : 3*d < ‖b/((u+1 : ℝ) : ℂ)‖-1 := by
    have hh := min_le_right δ (‖b/((u+1 : ℝ) : ℂ)‖-1)
    dsimp [d]
    linarith
  have ht := complex_matrix_spectralTilt_outlier_probability μ hm hv hp c hc hexp
    u L hu hL ν b d hd hgap
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  letI := flatSpectralMatrixTilt_probability μ (ν n) u hu b
  apply measureReal_mono ?_ (measure_ne_top _ _)
  rintro x hx ⟨w, hw, hs⟩
  exact hx ⟨w, lt_of_le_of_lt hw hdδ, hs⟩

/-- Change of measure for a disk event, with eventual positivity included. -/
lemma complex_local_exponential_lower_of_likelihood_cost
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (u L : ℝ) (hu : 0 < u) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℂ) (hb : 1 < ‖b/((u+1 : ℝ) : ℂ)‖) (δ : ℝ) (hδ : 0 < δ)
    (C : ℝ)
    (hcost : Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) u b).real
      {x | ENNReal.ofReal (Real.exp ((n : ℝ)*C)) < flatSpectralMatrixLikelihood μ (ν n) u b x})
      atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-C-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        (complexLocalEigenvalueEvent n (b/((u+1 : ℝ) : ℂ)) δ) := by
  let A := fun n => complexLocalEigenvalueEvent n (b/((u+1 : ℝ) : ℂ)) δ
  have hA (n : ℕ) : MeasurableSet (A n) := complexLocalEigenvalueEvent_measurable n _ δ
  have ht := complex_matrix_spectralTilt_local_probability μ hm hv hp c hc hexp
    u L hu hL ν b hb δ hδ
  letI : ∀ n, IsProbabilityMeasure (flatSpectralMatrixTilt μ (ν n) u b) :=
    fun n => flatSpectralMatrixTilt_probability μ (ν n) u hu b
  have hpos := original_event_eventually_positive (fun n => Fin n → Fin n → ℂ)
    (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (fun n => flatSpectralMatrixTilt μ (ν n) u b)
    (fun n => withDensity_absolutelyContinuous _ _) A hA ht
  have hlog := flatSpectralMatrixTilt_log_lower_from_cost μ u hu L ν b A hA ht C hcost ε hε
  filter_upwards [hlog, hpos, eventually_gt_atTop 0] with n hn hpn hn0
  exact exponential_lower_of_log_lower _ C ε n hpn hn0 hn

#print axioms complex_matrix_spectralTilt_local_probability
#print axioms complex_local_exponential_lower_of_likelihood_cost
end SpectralRadiusUpperTail
