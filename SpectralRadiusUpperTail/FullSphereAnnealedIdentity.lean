import SpectralRadiusUpperTail.FullSphereWeightMeasurable
import SpectralRadiusUpperTail.GaussianMatrixWeightIntegrable

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

lemma fullSphere_annealed_identity (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a) (z : ℂ) :
    (∫⁻ x : Fin n → Fin n → ℂ, fullSpectralSphereWeight n a z x
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) =
      ∫⁻ v : Fin n → ℂ, ENNReal.ofReal
        (∏ i : Fin n, gaussianFiniteNormalizer μ a v (spectralTiltTarget z (zeroExtendVector v) i))
        ∂haarDirectionLaw ℂ n := by
  letI := haarDirectionLaw_probability ℂ n hn
  have hj : Measurable (fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) =>
      ENNReal.ofReal (gaussianMatrixWeight a p.2
        (spectralTiltTarget z (zeroExtendVector p.2)) p.1)) :=
    ((gaussianSpectralWeight_joint_continuous a z).comp continuous_swap).measurable.ennreal_ofReal
  unfold fullSpectralSphereWeight
  rw [lintegral_lintegral_swap hj.aemeasurable]
  apply lintegral_congr
  intro v
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianMatrixWeight_integrable μ a ha v _)
    (Filter.Eventually.of_forall (fun x => (gaussianMatrixWeight_pos a v _ x).le)),
    gaussianMatrixWeight_integral]

#print axioms fullSphere_annealed_identity
end SpectralRadiusUpperTail
