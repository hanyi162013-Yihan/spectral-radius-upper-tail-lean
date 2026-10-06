import SpectralRadiusUpperTail.FlatSpectralJointEvent
import SpectralRadiusUpperTail.UniformSpectralTiltOutlier

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix ENNReal

lemma real_joint_spectralTilt_outlier_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℝ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖((b/(a+1) : ℝ) : ℂ)‖-1) :
    Tendsto (fun n => (flatSpectralJointTilt μ (ν n) (2*a) b).real
      (Set.univ ×ˢ {x | ¬ ∃ z ∈ closedBall ((b/(a+1) : ℝ) : ℂ) d, z ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)})) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*c) (by positivity) hexp 2)
  have hA (n : ℕ) : MeasurableSet ({x | ¬ ∃ z ∈ closedBall ((b/(a+1) : ℝ) : ℂ) d, z ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)} : Set (Fin n → Fin n → ℝ)) := by
    have hm : Measurable (fun x : Fin n → Fin n → ℝ => (normalizedArray x).map Complex.ofRealHom) :=
      (continuous_id.matrix_map Complex.continuous_ofReal).measurable.comp measurable_normalizedArray
    exact (measurableSet_matrix_outlier_event n ((b/(a+1) : ℝ) : ℂ) d).compl.preimage hm
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu := real_spectralTilt_outlier_uniform μ hm hvar c hc hexp
    a L ha hL b d hd hgap (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hu
  refine ⟨N,fun n hn => ?_⟩
  have hb := flatSpectralJointTilt_event_le μ (ν n) (2*a) (by positivity) b
    {x | ¬ ∃ z ∈ closedBall ((b/(a+1) : ℝ) : ℂ) d, z ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)} (hA n) (ENNReal.ofReal (ε/2)) (by
      intro v
      letI := gaussianTiltedMatrixLaw_probability μ hX hm hvar (zeroExtendVector v.val)
        (by simpa only [zeroExtendVector_fin] using v.property.1) (2*a) (by positivity)
        (spectralTiltTarget (n := n) b (zeroExtendVector v.val))
      have hh := (hN n hn v.val v.property).le
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
        (by simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ε/2),Measure.real] using hh))
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ ε/2)] at hr
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
  change (flatSpectralJointTilt μ (ν n) (2*a) b _).toReal < ε
  linarith

#print axioms real_joint_spectralTilt_outlier_probability
end SpectralRadiusUpperTail
