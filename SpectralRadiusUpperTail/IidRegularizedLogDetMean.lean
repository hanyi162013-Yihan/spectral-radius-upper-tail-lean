import SpectralRadiusUpperTail.IidRegularizedLogDetLower
import SpectralRadiusUpperTail.IidRegularizedLogDetIntegrable
import SpectralRadiusUpperTail.LowerMeanFromProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The lower expectation input for bulk concentration, with integrability proved
from the original entry law. -/
lemma iid_regularizedLogDet_mean_lower (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (b s ε : ℝ) (hb : 1 < b) (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2*Real.log b-ε ≤
      ∫ x : Fin n × Fin n → ℂ, matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)
        ∂Measure.pi (fun _ => μ) := by
  apply eventually_integral_lower_of_probability (fun n => Fin n × Fin n → ℂ)
    (fun n => Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun n x => matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ))
    (fun n => ((matrixRegularizedLogDet_measurable n b s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const (n : ℝ))
    (Eventually.of_forall (fun n => (iidRegularizedLogDet_integrable μ c hc hexp n b s hs).div_const _))
    (min 0 (Real.log s)) (2*Real.log b) _ _ ε hε
  · intro n x
    by_cases hn : n = 0
    · subst n
      simpa only [Nat.cast_zero, div_zero] using min_le_left (0 : ℝ) (Real.log s)
    · exact (min_le_right _ _).trans (normalized_matrixRegularizedLogDet_floor
        (Nat.pos_of_ne_zero hn) (normalizedIidMatrix x) b s hs)
  · intro δ hδ
    exact iid_regularizedLogDet_lower_probability μ c hc hexp hm hv b s δ hb hs.le hδ

#print axioms iid_regularizedLogDet_mean_lower
end SpectralRadiusUpperTail
