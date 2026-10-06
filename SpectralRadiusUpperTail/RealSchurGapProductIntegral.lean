import SpectralRadiusUpperTail.RealSchurNativeGapKernel
import SpectralRadiusUpperTail.FiniteProductMeasureScale
import SpectralRadiusUpperTail.PiRealDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

theorem realSchurNativeGapDensity_integrable (q : ℕ) (n u : ℝ)
    (hn : 0 < n) (hu : q=2 → 0 < u) :
    Integrable (realSchurNativeGapDensity q n u) (realSchurNativeAuxiliaryBase q) := by
  let := realSchurNativeGapLaw_probability q n u hn hu
  apply (lintegral_ofReal_ne_top_iff_integrable
    (realSchurNativeGapDensity_measurable q n u).aestronglyMeasurable
    (Filter.Eventually.of_forall (realSchurNativeGapDensity_nonneg q n u))).mp
  have hh := congrArg (fun μ : Measure ℝ => μ Set.univ)
    (realSchurNativeGapDensity_measure q n u hn hu)
  rw [withDensity_apply _ MeasurableSet.univ,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] at hh
  simp only [Measure.restrict_univ] at hh
  rw [hh]
  exact realSchurNativeGapNormalizer_ne_top q n u hn hu

/-- Simultaneous normalization of every native gap coordinate produces
exactly the independent product of the model's probability laws. -/
theorem realSchurNativeGapProduct_lintegral
    {m : ℕ} (s : Fin m → ℕ) (n : ℝ) (hn : 0 < n) (u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i)
    (H : (Fin m → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ g, ENNReal.ofReal (∏ i : Fin m, realSchurNativeGapDensity (s i) n (u i) (g i))*H g
      ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (s i))) =
        (∏ i : Fin m, realSchurNativeGapNormalizer (s i) n (u i))*
          ∫⁻ g, H g ∂Measure.pi (fun i => realSchurNativeGapLaw (s i) n (u i)) := by
  let : ∀ i, IsProbabilityMeasure (realSchurNativeGapLaw (s i) n (u i)) :=
    fun i => realSchurNativeGapLaw_probability (s i) n (u i) hn (hu i)
  have hw : Measurable (fun g : Fin m → ℝ =>
      ENNReal.ofReal (∏ i : Fin m, realSchurNativeGapDensity (s i) n (u i) (g i))) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i _
    exact (realSchurNativeGapDensity_measurable (s i) n (u i)).comp (measurable_pi_apply i)
  change (∫⁻ g, ((fun g : Fin m → ℝ =>
    ENNReal.ofReal (∏ i : Fin m, realSchurNativeGapDensity (s i) n (u i) (g i)))*H) g
      ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (s i)))=_
  rw [← lintegral_withDensity_eq_lintegral_mul _ hw hH,
    pi_withDensity_ofReal (fun i => realSchurNativeAuxiliaryBase (s i))
      (fun i => realSchurNativeGapDensity (s i) n (u i))
      (fun i => realSchurNativeGapDensity_integrable (s i) n (u i) hn (hu i))
      (fun i => realSchurNativeGapDensity_nonneg (s i) n (u i))]
  simp_rw [realSchurNativeGapDensity_measure _ n _ hn (hu _)]
  rw [finite_pi_measure_smul (fun i => realSchurNativeGapLaw (s i) n (u i))
    (fun i => realSchurNativeGapNormalizer (s i) n (u i))
    (fun i => realSchurNativeGapNormalizer_ne_top (s i) n (u i) hn (hu i)),lintegral_smul_measure,smul_eq_mul]

#print axioms realSchurNativeGapDensity_integrable
#print axioms realSchurNativeGapProduct_lintegral
end SpectralRadiusUpperTail
