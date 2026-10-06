import SpectralRadiusUpperTail.SchurGapLaw
import SpectralRadiusUpperTail.ExponentialFirstMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The normalizer of the product-model gap kernel, prior to identifying
that product model with any actual matrix distribution. -/
noncomputable def schurGapKernelNormalizer (n y : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, ENNReal.ofReal (schurGapWeight y s) ∂expMeasure (n/2)

noncomputable def schurGapExplicitDensity (n y s : ℝ) : ℝ≥0∞ :=
  exponentialPDF (n/2) s *
    (ENNReal.ofReal (schurGapWeight y s) /
      schurGapKernelNormalizer n y)

/-- The already-defined squared-gap model law has a literal Lebesgue
density: exponential base density times the inverse-square-root gap weight,
divided by its exact normalizer. -/
theorem schurSquaredGapLaw_eq_explicitDensity (n y : ℝ) :
    schurSquaredGapLaw n y =
      (volume : Measure ℝ).withDensity (schurGapExplicitDensity n y) := by
  unfold schurSquaredGapLaw normalizedTilt schurGapExplicitDensity
    schurGapKernelNormalizer
  rw [expMeasure_eq_density]
  symm
  exact withDensity_mul volume
    (measurable_exponentialPDFReal (n/2)).ennreal_ofReal
    ((schurGapWeight_measurable y).ennreal_ofReal.div_const _)

theorem schurGapExplicitDensity_of_pos (n y s : ℝ)
    (hn : 0 < n) (hy : 0 < y) (hs : 0 ≤ s) :
    schurGapExplicitDensity n y s =
      ENNReal.ofReal ((n/2)*Real.exp (-(n/2)*s)) *
        (ENNReal.ofReal ((Real.sqrt (s+4*y^2))⁻¹) /
          schurGapKernelNormalizer n y) := by
  unfold schurGapExplicitDensity schurGapWeight
  rw [exponentialPDF_of_nonneg hs]
  simp [max_eq_right hs]

#print axioms schurSquaredGapLaw_eq_explicitDensity
#print axioms schurGapExplicitDensity_of_pos
end SpectralRadiusUpperTail
