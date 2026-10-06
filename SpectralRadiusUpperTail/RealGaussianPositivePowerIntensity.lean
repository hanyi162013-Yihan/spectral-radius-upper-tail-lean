import SpectralRadiusUpperTail.RealGaussianRealIntensity
import SpectralRadiusUpperTail.RealGaussianSubstatIntegrable

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal BigOperators

/-- The actual positive-real exterior power statistic integrates the
corresponding scalar weight against the real eigenvalue intensity. -/
theorem realGaussianPositivePower_ofReal_eq_intensity
    (n k : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (∫ a, realGaussianPositiveRealExteriorPower n k a
      ∂gaussianMatrixLaw n) =
      ∫⁻ x : ℝ, (if 1 < x then ENNReal.ofReal (x^(2*k)) else 0)
        ∂realGaussianRealIntensity n := by
  have hw : Measurable (fun x : ℝ =>
      if 1 < x then ENNReal.ofReal (x^(2*k)) else 0) := by
    change Measurable ((Set.Ioi (1 : ℝ)).indicator
      (fun x : ℝ => ENNReal.ofReal (x^(2*k))))
    exact (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (x^(2*k)))).indicator measurableSet_Ioi
  have hnonneg : ∀ a, 0 ≤ realGaussianPositiveRealExteriorPower n k a := by
    intro a
    exact (matrixPositiveRealExteriorPower_nonneg_le_total _ k).1
  rw [ofReal_integral_eq_lintegral_ofReal
    (realGaussianPositiveRealExteriorPower_integrable n k hn)
    (Filter.Eventually.of_forall hnonneg)]
  rw [realGaussianRealIntensity, realLabelIntensity_lintegral _ _ _
    (realGaussianNormalizedSpectrum_measurable n) _ hw]
  apply lintegral_congr_ae
  filter_upwards [realGaussianMeasurableNormalizedSpectrum_roots_ae n hn] with a ha
  change ENNReal.ofReal (((((1/Real.sqrt (n : ℝ)) • Matrix.of a.curry).map
    Complex.ofRealHom).charpoly.roots.map (fun z : ℂ =>
      if z.im = 0 ∧ 1 < z.re then z.re^(2*k) else 0)).sum) = _
  rw [ha, Multiset.map_map]
  change ENNReal.ofReal (∑ i : Fin n,
    if (realGaussianNormalizedSpectrum n a i).im = 0 ∧
      1 < (realGaussianNormalizedSpectrum n a i).re
    then (realGaussianNormalizedSpectrum n a i).re^(2*k) else 0) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    split_ifs with hi
    · exact pow_nonneg (by linarith [hi.2]) _
    · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases he : (realGaussianNormalizedSpectrum n a i).im = 0 <;>
    by_cases hp : 1 < (realGaussianNormalizedSpectrum n a i).re <;>
      simp [he,hp]

#print axioms realGaussianPositivePower_ofReal_eq_intensity
end SpectralRadiusUpperTail
