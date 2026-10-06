import SpectralRadiusUpperTail.FlatSpectralMatrixException
import SpectralRadiusUpperTail.ComplexJointTiltNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma complex_spectralTilt_quadratic_exception
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (L : ℝ) (hL : 0 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℂ)
    (E : (n : ℕ) → Set (Fin n → Fin n → ℂ)) (hE : ∀ n, MeasurableSet (E n))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hbad : ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real (E n) ≤
        C*Real.exp (-c*(n : ℝ)^2)) :
    Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real (E n)) atTop (𝓝 0) := by
  exact flatSpectralMatrixTilt_quadratic_exception μ a ha L ν b _
    (complex_joint_spectralTilt_logNormalizer_limit μ hm hvar hpseudo τ hτ hexp a ha L hL ν b)
    E hE C c hC hc hbad

#print axioms complex_spectralTilt_quadratic_exception
end SpectralRadiusUpperTail
