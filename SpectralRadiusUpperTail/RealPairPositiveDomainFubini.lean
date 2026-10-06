import SpectralRadiusUpperTail.RealPairPositivePolarIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- The positive polar domain has r>0 and the entire skew half-line q>r. -/
theorem realPair_positiveDomain_lintegral
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in realSchurPositivePairDomain, f z) =
      ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ q in Set.Ioi r, f (q,r) := by
  have hS := realSchurPositivePairDomain_isOpen.measurableSet
  rw [← lintegral_indicator hS]
  change (∫⁻ z, realSchurPositivePairDomain.indicator f z
    ∂(volume : Measure ℝ).prod volume)=_
  rw [lintegral_prod_symm _ (hf.indicator hS).aemeasurable]
  have hp (r : ℝ) :
      (∫⁻ q, realSchurPositivePairDomain.indicator f (q,r)) =
        (Set.Ioi (0 : ℝ)).indicator (fun r => ∫⁻ q in Set.Ioi r, f (q,r)) r := by
    by_cases hr : 0 < r
    · rw [Set.indicator_of_mem (show r ∈ Set.Ioi (0 : ℝ) from hr),← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro q
      simp [realSchurPositivePairDomain,Set.indicator_apply,hr]
    · rw [Set.indicator_of_notMem (show r ∉ Set.Ioi (0 : ℝ) from hr)]
      have hz (q : ℝ) : realSchurPositivePairDomain.indicator f (q,r)=0 := by
        simp [realSchurPositivePairDomain,Set.indicator_apply,hr]
      simp_rw [hz]
      exact lintegral_zero
  simp_rw [hp]
  exact lintegral_indicator measurableSet_Ioi _

#print axioms realPair_positiveDomain_lintegral
end SpectralRadiusUpperTail
