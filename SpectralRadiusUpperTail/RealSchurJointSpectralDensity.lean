import SpectralRadiusUpperTail.RealSchurNativeSpectralDensity
import SpectralRadiusUpperTail.FiniteTripleProductIntegral
import SpectralRadiusUpperTail.PiRealDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- The joint native-block coordinate law has the product of the
explicit scalar and nonreal-pair densities. -/
theorem realSchurNativeSpectralProduct_eq_density
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (n : ℝ) (hn : 0 < n) :
    Measure.pi (fun i => realSchurNativeSpectralMeasure (s i) n) =
      (Measure.pi (fun i => realSchurNativeSpectralBase (s i))).withDensity
        (fun v => ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralDensity (s i) n (v i))) := by
  simp_rw [realSchurNativeSpectralMeasure_eq_density _ (hs _) n]
  exact (pi_withDensity_ofReal (fun i => realSchurNativeSpectralBase (s i))
    (fun i => realSchurNativeSpectralDensity (s i) n)
    (fun i => realSchurNativeSpectralDensity_integrable (s i) (hs i) n hn)
    (fun i => realSchurNativeSpectralDensity_nonneg (s i) n)).symm

/-- Regrouping separates the real parts, squared imaginary parts and
gaps, while preserving the actual independent native-block measure. -/
theorem realSchurNativeSpectralProduct_lintegral
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (n : ℝ) (hn : 0 < n)
    (H : (Fin m → ℝ × (ℝ × ℝ)) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ v, H v ∂Measure.pi (fun i => realSchurNativeSpectralMeasure (s i) n)) =
      ∫⁻ x : Fin m → ℝ, ∫⁻ u, ∫⁻ g,
        ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralDensity (s i) n (x i,u i,g i))*
          H (fun i => (x i,u i,g i))
        ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (s i))
        ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (s i)) := by
  have hw : Measurable (fun v : Fin m → ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralDensity (s i) n (v i))) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i _
    exact (realSchurNativeSpectralDensity_measurable (s i) n).comp (measurable_pi_apply i)
  rw [realSchurNativeSpectralProduct_eq_density s hs n hn,
    lintegral_withDensity_eq_lintegral_mul _ hw hH]
  change (∫⁻ v, ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralDensity (s i) n (v i))*H v
    ∂Measure.pi (fun i => (volume : Measure ℝ).prod
      ((realSchurNativeAuxiliaryBase (s i)).prod (realSchurNativeAuxiliaryBase (s i)))))=_
  exact finite_triple_product_lintegral (fun _ => (volume : Measure ℝ))
    (fun i => realSchurNativeAuxiliaryBase (s i)) (fun i => realSchurNativeAuxiliaryBase (s i))
    (fun v => ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralDensity (s i) n (v i))*H v) (hw.mul hH)

#print axioms realSchurNativeSpectralProduct_eq_density
#print axioms realSchurNativeSpectralProduct_lintegral
end SpectralRadiusUpperTail
