import SpectralRadiusUpperTail.IidUniformRegularizedMeanUpper
import SpectralRadiusUpperTail.BulkLogDetIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_complex_regularizedResidualLogDet_integral (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (z : ℂ) (s : ℝ) :
    (∫ x : Fin n → Fin n → ℂ, regularizedResidualLogDet x z s/(n : ℝ)
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) =
    ∫ x : Fin n × Fin n → ℂ, complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ)
      ∂Measure.pi (fun _ => μ) := by
  have hm : Measurable (fun x : Fin n × Fin n → ℂ =>
      complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ)) :=
    ((complexRegularizedLogDet_measurable n z s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _
  rw [← iid_matrix_flatten_law μ n, integral_map
    (show Measurable (fun x : Fin n → Fin n → ℂ => fun ij : Fin n × Fin n => x ij.1 ij.2) by fun_prop).aemeasurable
    hm.aestronglyMeasurable]
  simp only [normalizedIidMatrix_flatten_eq]
  rfl

lemma complex_bulk_logDet_mean_upper_uniform (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r) :
    ∃ M : ℝ, 0 < M ∧ ∀ R s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
        (∫ x : Fin n → Fin n → ℂ, regularizedResidualLogDet x z s/(n : ℝ)
          ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ 2*Real.log ‖z‖+s*M^2+ε := by
  simpa only [iid_complex_regularizedResidualLogDet_integral] using
    iid_uniform_regularizedLogDet_mean_upper μ c hc hexp hm hv r hr

#print axioms iid_complex_regularizedResidualLogDet_integral
#print axioms complex_bulk_logDet_mean_upper_uniform
end SpectralRadiusUpperTail
