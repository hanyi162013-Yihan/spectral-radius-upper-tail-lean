import SpectralRadiusUpperTail.IidRegularizedLogDetMeanUpper
import SpectralRadiusUpperTail.BulkLogDetIdentity
import SpectralRadiusUpperTail.RealBulkLogDetIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma complex_bulk_logDet_mean_upper (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (b : ℝ) (hb : 1 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (∫ x : Fin n → Fin n → ℂ, regularizedResidualLogDet x (b : ℂ) s/(n : ℝ)
          ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ 2*Real.log b+s*M^2+ε := by
  simpa only [iid_regularizedResidualLogDet_integral] using
    iid_regularizedLogDet_mean_upper μ c hc hexp hm hv b hb

lemma real_bulk_logDet_mean_upper (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℝ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℝ, z ∂μ) = 0) (hv : (∫ z : ℝ, ‖z‖^2 ∂μ) = 1)
    (b : ℝ) (hb : 1 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (∫ x : Fin n → Fin n → ℝ, regularizedResidualLogDet x b s/(n : ℝ)
          ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ 2*Real.log b+s*M^2+ε := by
  have hh := complex_bulk_logDet_mean_upper (complexifiedLaw μ) c hc
    (complexifiedLaw_squareExp μ c hexp)
    (by rw [complexifiedLaw_mean, hm]; rfl)
    (by rw [complexifiedLaw_energy, hv]) b hb
  simpa only [real_regularizedResidualLogDet_integral_complexify] using hh

#print axioms complex_bulk_logDet_mean_upper
#print axioms real_bulk_logDet_mean_upper
end SpectralRadiusUpperTail
