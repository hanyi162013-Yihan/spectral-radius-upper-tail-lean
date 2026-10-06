import SpectralRadiusUpperTail.IidRegularizedLogDetMean
import SpectralRadiusUpperTail.BulkLogDetIdentity
import SpectralRadiusUpperTail.RealBulkLogDetIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma complex_bulk_logDet_mean_lower (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (b s ε : ℝ) (hb : 1 < b) (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2*Real.log b-ε ≤
      ∫ x : Fin n → Fin n → ℂ, regularizedResidualLogDet x (b : ℂ) s/(n : ℝ)
        ∂Measure.pi (fun _ => Measure.pi (fun _ => μ)) := by
  simpa only [iid_regularizedResidualLogDet_integral] using
    iid_regularizedLogDet_mean_lower μ c hc hexp hm hv b s ε hb hs hε

lemma real_bulk_logDet_mean_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℝ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℝ, z ∂μ) = 0) (hv : (∫ z : ℝ, ‖z‖^2 ∂μ) = 1)
    (b s ε : ℝ) (hb : 1 < b) (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2*Real.log b-ε ≤
      ∫ x : Fin n → Fin n → ℝ, regularizedResidualLogDet x b s/(n : ℝ)
        ∂Measure.pi (fun _ => Measure.pi (fun _ => μ)) := by
  have hh := complex_bulk_logDet_mean_lower (complexifiedLaw μ) c hc
    (complexifiedLaw_squareExp μ c hexp)
    (by rw [complexifiedLaw_mean, hm]; rfl)
    (by rw [complexifiedLaw_energy, hv]) b s ε hb hs hε
  simpa only [real_regularizedResidualLogDet_integral_complexify] using hh

#print axioms complex_bulk_logDet_mean_lower
#print axioms real_bulk_logDet_mean_lower
end SpectralRadiusUpperTail
