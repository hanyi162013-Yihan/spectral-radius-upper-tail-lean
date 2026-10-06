import SpectralRadiusUpperTail.FullSphereAnnealedIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory Metric WithLp
open scoped ENNReal BigOperators

lemma spectral_row_normalizer_product_measurable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (a : ℝ) (z : ℂ) :
    Measurable (fun v : Fin n → ℂ => ∏ i : Fin n,
      gaussianFiniteNormalizer μ a v (spectralTiltTarget z (zeroExtendVector v) i)) := by
  simp_rw [← gaussianMatrixWeight_integral μ a]
  exact (gaussianSpectralWeight_joint_continuous a z).stronglyMeasurable.integral_prod_right'.measurable

lemma fullSphere_annealed_sphere_identity (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a) (z : ℂ) :
    (∫⁻ x : Fin n → Fin n → ℂ, fullSpectralSphereWeight n a z x
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) =
      ∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1, ENNReal.ofReal
        (∏ i : Fin n, gaussianFiniteNormalizer μ a (ofLp v.val)
          (spectralTiltTarget z (zeroExtendVector (ofLp v.val)) i))
        ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  rw [fullSphere_annealed_identity μ n hn a ha z, haarDirectionLaw,
    lintegral_map (spectral_row_normalizer_product_measurable μ n a z).ennreal_ofReal (by fun_prop)]

#print axioms spectral_row_normalizer_product_measurable
#print axioms fullSphere_annealed_sphere_identity
end SpectralRadiusUpperTail
