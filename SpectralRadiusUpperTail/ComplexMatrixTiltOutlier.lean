import SpectralRadiusUpperTail.ComplexJointTiltOutlier
import SpectralRadiusUpperTail.FlatSpectralMatrixTilt
import SpectralRadiusUpperTail.OutlierSpectralRadius

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix ENNReal

lemma complex_matrix_spectralTilt_outlier_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖(b/((a+1 : ℝ) : ℂ))‖-1) :
    Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real
      {x | ¬ ∃ z ∈ closedBall (b/((a+1 : ℝ) : ℂ)) d, z ∈ spectrum ℂ (normalizedArray x)}) atTop (𝓝 0) := by
  have ht := complex_joint_spectralTilt_outlier_probability μ hm hvar hpseudo c hc hexp
    a L ha hL ν b d hd hgap
  convert ht using 1
  funext n
  unfold Measure.real
  rw [flatSpectralMatrixTilt_event μ (ν n) a (by positivity) b _ (by
    exact (measurableSet_matrix_outlier_event n (b/((a+1 : ℝ) : ℂ)) d).compl.preimage measurable_normalizedArray)]

lemma complex_matrix_spectralTilt_radius_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℂ) (r : ℝ) (hr : 1 < r) (hb : r < ‖(b/((a+1 : ℝ) : ℂ))‖) :
    Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real
      {x | (spectralRadius ℂ (normalizedArray x)).toReal ≤ r}) atTop (𝓝 0) := by
  obtain ⟨d,hd,hgap,hdr⟩ := outlier_disk_above_radius (b/((a+1 : ℝ) : ℂ)) r hr hb
  have ht := complex_matrix_spectralTilt_outlier_probability μ hm hvar hpseudo c hc hexp
    a L ha hL ν b d hd hgap
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  letI := flatSpectralMatrixTilt_probability μ (ν n) a (by positivity) b
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx ho
  exact (not_lt_of_ge hx) (spectralRadius_gt_of_outlier (normalizedArray x) (b/((a+1 : ℝ) : ℂ)) d r hdr ho)

#print axioms complex_matrix_spectralTilt_outlier_probability
#print axioms complex_matrix_spectralTilt_radius_probability
end SpectralRadiusUpperTail
