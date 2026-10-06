import SpectralRadiusUpperTail.FlatSpectralMatrixException
import SpectralRadiusUpperTail.RealJointTiltNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma real_spectralTilt_quadratic_exception
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℝ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (L : ℝ) (hL : 0 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℝ)
    (E : (n : ℕ) → Set (Fin n → Fin n → ℝ)) (hE : ∀ n, MeasurableSet (E n))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hbad : ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real (E n) ≤
        C*Real.exp (-c*(n : ℝ)^2)) :
    Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real (E n)) atTop (𝓝 0) := by
  exact flatSpectralMatrixTilt_quadratic_exception μ a ha L ν b _
    (real_joint_spectralTilt_logNormalizer_limit μ hm hvar τ hτ hexp a ha L hL ν b)
    E hE C c hC hc hbad

#print axioms real_spectralTilt_quadratic_exception
end SpectralRadiusUpperTail
