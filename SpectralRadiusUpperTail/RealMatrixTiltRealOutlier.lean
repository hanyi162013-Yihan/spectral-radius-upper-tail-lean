import SpectralRadiusUpperTail.RealJointTiltRealOutlier
import SpectralRadiusUpperTail.FlatSpectralMatrixTilt

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix ENNReal

lemma real_matrix_spectralTilt_real_outlier_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℝ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖((b/(a+1) : ℝ) : ℂ)‖-1) :
    Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) (2*a) b).real
      {x | ¬ ∃ z : ℝ, (z : ℂ) ∈ closedBall ((b/(a+1) : ℝ) : ℂ) d ∧ (z : ℂ) ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)}) atTop (𝓝 0) := by
  have ht := real_joint_spectralTilt_real_outlier_probability μ hm hvar c hc hexp
    a L ha hL ν b d hd hgap
  convert ht using 1
  funext n
  unfold Measure.real
  rw [flatSpectralMatrixTilt_event μ (ν n) (2*a) (by positivity) b _ (by
    have hm : Measurable (fun x : Fin n → Fin n → ℝ => (normalizedArray x).map Complex.ofRealHom) :=
      (continuous_id.matrix_map Complex.continuous_ofReal).measurable.comp measurable_normalizedArray
    exact (measurableSet_matrix_real_outlier_event n (b/(a+1)) d).compl.preimage hm)]


#print axioms real_matrix_spectralTilt_real_outlier_probability
end SpectralRadiusUpperTail
