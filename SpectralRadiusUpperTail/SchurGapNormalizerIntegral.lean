import SpectralRadiusUpperTail.RealSchurGapErfcCorrection
import SpectralRadiusUpperTail.RealSchurGapLawExplicitDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The product-model normalizer is the finite real expectation of its
positive squared-gap weight. -/
theorem schurGapKernelNormalizer_eq_ofReal (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    schurGapKernelNormalizer n y =
      ENNReal.ofReal (∫ s : ℝ, schurGapWeight y s ∂expMeasure (n/2)) := by
  haveI := isProbabilityMeasure_expMeasure (show 0 < n/2 by positivity)
  unfold schurGapKernelNormalizer
  exact (ofReal_integral_eq_lintegral_ofReal
    (schurGapWeight_integrable _ y hy)
    (Filter.Eventually.of_forall (fun s => (schurGapWeight_positive y hy s).le))).symm

/-- The exponential base law turns the squared-gap normalizer into the
Lebesgue integral evaluated by the Gaussian-tail substitution. -/
theorem schurGapWeight_exp_integral (n y : ℝ)
    (hn : 0 < n) :
    (∫ s : ℝ, schurGapWeight y s ∂expMeasure (n/2)) =
      (n/2) * (∫ s : ℝ in Ioi 0,
        Real.exp (-(n/2)*s) *
          (Real.sqrt (s+4*y^2))⁻¹) := by
  have hd : Measurable (exponentialPDF (n/2)) :=
    (measurable_exponentialPDFReal (n/2)).ennreal_ofReal
  have hfinite : ∀ᵐ s : ℝ ∂(volume : Measure ℝ),
      exponentialPDF (n/2) s < ∞ :=
    Filter.Eventually.of_forall (fun s => ENNReal.ofReal_lt_top)
  have hpoint (s : ℝ) :
      (exponentialPDF (n/2) s).toReal * schurGapWeight y s =
      (Ici (0:ℝ)).indicator
        (fun s : ℝ => (n/2)*Real.exp (-(n/2)*s) *
          (Real.sqrt (s+4*y^2))⁻¹) s := by
    by_cases hs : 0 ≤ s
    · rw [Set.indicator_of_mem (show s ∈ Ici (0:ℝ) from hs),
        exponentialPDF_of_nonneg hs,
        ENNReal.toReal_ofReal (by positivity)]
      simp only [schurGapWeight, max_eq_right hs]
      ring
    · rw [Set.indicator_of_notMem (show s ∉ Ici (0:ℝ) from hs),
        exponentialPDF_of_neg (lt_of_not_ge hs)]
      simp
  calc
    (∫ s : ℝ, schurGapWeight y s ∂expMeasure (n/2)) =
      ∫ s : ℝ, (exponentialPDF (n/2) s).toReal * schurGapWeight y s := by
        rw [expMeasure_eq_density,
          integral_withDensity_eq_integral_toReal_smul hd hfinite]
        simp only [smul_eq_mul]
    _ = ∫ s : ℝ in Ici 0,
          (n/2)*Real.exp (-(n/2)*s) *
            (Real.sqrt (s+4*y^2))⁻¹ := by
        simp_rw [hpoint]
        rw [integral_indicator measurableSet_Ici]
    _ = ∫ s : ℝ in Ioi 0,
          (n/2)*Real.exp (-(n/2)*s) *
            (Real.sqrt (s+4*y^2))⁻¹ := by
        rw [integral_Ici_eq_integral_Ioi]
    _ = _ := by
      rw [← integral_const_mul]
      congr 1
      funext s
      ring

/-- Exact normalizer of the positive squared-gap product model. The
factor `2*y` is the angular Jacobian scale for a nonreal pair. -/
theorem schurGapKernelNormalizer_eq_erfcCorrection (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    schurGapKernelNormalizer n y =
      ENNReal.ofReal
        (gaussianErfcCorrection (Real.sqrt (2*n)*y)/(2*y)) := by
  rw [schurGapKernelNormalizer_eq_ofReal n y hn hy,
    schurGapWeight_exp_integral n y hn]
  congr 1
  have h := schur_gap_integral_eq_erfc_correction n y hn hy
  apply (eq_div_iff (by positivity : (2*y) ≠ 0)).mpr
  calc
    (n/2) * (∫ s : ℝ in Ioi 0,
        Real.exp (-(n/2)*s) *
          (Real.sqrt (s+4*y^2))⁻¹) * (2*y) =
      n*y * (∫ s : ℝ in Ioi 0,
        Real.exp (-(n/2)*s) *
          (Real.sqrt (s+4*y^2))⁻¹) := by ring
    _ = _ := h

/-- Fully explicit positive squared-gap density, with the erfc
normalizer exposed in the formula. -/
noncomputable def schurGapErfcDensity (n y s : ℝ) : ℝ≥0∞ :=
  exponentialPDF (n/2) s *
    (ENNReal.ofReal (schurGapWeight y s) /
      ENNReal.ofReal
        (gaussianErfcCorrection (Real.sqrt (2*n)*y)/(2*y)))

theorem schurSquaredGapLaw_eq_erfcDensity (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    schurSquaredGapLaw n y =
      (volume : Measure ℝ).withDensity (schurGapErfcDensity n y) := by
  rw [schurSquaredGapLaw_eq_explicitDensity]
  congr 1
  funext s
  simp only [schurGapExplicitDensity, schurGapErfcDensity,
    schurGapKernelNormalizer_eq_erfcCorrection n y hn hy]

theorem schurGapErfcDensity_lintegral_eq_one (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    (∫⁻ s : ℝ, schurGapErfcDensity n y s) = 1 := by
  haveI := schurSquaredGapLaw_probability n y hn hy
  have h := (measure_univ : schurSquaredGapLaw n y Set.univ = 1)
  rw [schurSquaredGapLaw_eq_erfcDensity n y hn hy,
    withDensity_apply _ MeasurableSet.univ] at h
  simpa using h

theorem schurGapErfcDensity_mean_le (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    (∫ s : ℝ, s ∂(volume : Measure ℝ).withDensity
      (schurGapErfcDensity n y)) ≤ 2/n := by
  rw [← schurSquaredGapLaw_eq_erfcDensity n y hn hy]
  exact schurSquaredGapLaw_mean_le n y hn hy

#print axioms schurGapKernelNormalizer_eq_ofReal
#print axioms schurGapWeight_exp_integral
#print axioms schurGapKernelNormalizer_eq_erfcCorrection
#print axioms schurSquaredGapLaw_eq_erfcDensity
#print axioms schurGapErfcDensity_lintegral_eq_one
#print axioms schurGapErfcDensity_mean_le
end SpectralRadiusUpperTail
