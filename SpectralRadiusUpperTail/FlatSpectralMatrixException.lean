import SpectralRadiusUpperTail.FlatSpectralMatrixWeight
import SpectralRadiusUpperTail.NormalizedTiltExceptionLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma flatSpectralMatrixTilt_quadratic_exception
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (L : ℝ)
    (ν : (n : ℕ) → Measure (flatUnitDirections 𝕂 n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : 𝕂) (A : ℝ)
    (hZ : Tendsto (fun n => Real.log (∫ p, flatSpectralJointWeight a b p
      ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))/(n : ℝ))
      atTop (𝓝 A))
    (E : (n : ℕ) → Set (Fin n → Fin n → 𝕂)) (hE : ∀ n, MeasurableSet (E n))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hbad : ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real (E n) ≤
        C*Real.exp (-c*(n : ℝ)^2)) :
    Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real (E n)) atTop (𝓝 0) := by
  apply normalizedTilt_quadratic_exception_tendsto
    (fun n => Fin n → Fin n → 𝕂)
    (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (fun n => flatSpectralMatrixWeight (ν n) a b)
    (fun n x => flatSpectralMatrixWeight_le_one (ν n) a ha b x)
    (fun n => ∫ p, flatSpectralJointWeight a b p
      ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))
  · intro n
    exact integral_exp_pos (flatSpectralJointWeight_integrable μ (ν n) a ha b)
  · exact fun n => flatSpectralMatrixWeight_normalizer μ (ν n) a ha b
  · exact hZ
  · exact hE
  · exact hC
  · exact hc
  · exact hbad

#print axioms flatSpectralMatrixTilt_quadratic_exception
end SpectralRadiusUpperTail
