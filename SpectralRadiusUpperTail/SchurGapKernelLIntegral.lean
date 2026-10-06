import SpectralRadiusUpperTail.SchurGapNormalizerIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem schurGapExplicitDensity_measurable (n y : ℝ) :
    Measurable (schurGapExplicitDensity n y) :=
  (measurable_exponentialPDFReal (n/2)).ennreal_ofReal.mul
    ((schurGapWeight_measurable y).ennreal_ofReal.div_const _)

/-- Integration under the normalized gap law, with its raw positive
Lebesgue kernel and normalizing factor displayed separately. -/
theorem schurSquaredGapLaw_lintegral_kernel
    (n y : ℝ) (hn : 0 < n) (hy : 0 < y)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ s, g s ∂schurSquaredGapLaw n y) =
      (ENNReal.ofReal (n/2) / schurGapKernelNormalizer n y) *
        ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(n/2)*s)) *
            ENNReal.ofReal ((Real.sqrt (s+4*y^2))⁻¹) * g s := by
  classical
  let C := ENNReal.ofReal (n/2) / schurGapKernelNormalizer n y
  have hZ : schurGapKernelNormalizer n y ≠ 0 := by
    rw [schurGapKernelNormalizer_eq_ofReal n y hn hy]
    exact (ENNReal.ofReal_pos.mpr (schurGapWeight_normalizer_pos n y hn hy)).ne'
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr hZ)
  have hp (s : ℝ) : schurGapExplicitDensity n y s * g s =
      (Set.Ici (0 : ℝ)).indicator
        (fun s => C * (ENNReal.ofReal (Real.exp (-(n/2)*s)) *
          ENNReal.ofReal ((Real.sqrt (s+4*y^2))⁻¹) * g s)) s := by
    by_cases hs : 0 ≤ s
    · rw [Set.indicator_of_mem (show s ∈ Set.Ici (0 : ℝ) from hs),
        schurGapExplicitDensity_of_pos n y s hn hy hs,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ n/2)]
      dsimp only [C]
      simp only [div_eq_mul_inv]
      ac_rfl
    · rw [Set.indicator_of_notMem (show s ∉ Set.Ici (0 : ℝ) from hs)]
      simp [schurGapExplicitDensity,exponentialPDF_of_neg (lt_of_not_ge hs)]
  rw [schurSquaredGapLaw_eq_explicitDensity,
    lintegral_withDensity_eq_lintegral_mul volume
      (schurGapExplicitDensity_measurable n y) hg]
  change (∫⁻ s, schurGapExplicitDensity n y s * g s) = _
  simp_rw [hp]
  rw [lintegral_indicator measurableSet_Ici,
    setLIntegral_congr (Ioi_ae_eq_Ici (μ := (volume : Measure ℝ)) (a := 0)).symm,
    lintegral_const_mul' C _ hC]

/-- The unnormalized Gaussian gap kernel is a finite positive constant
times the probability law used in the Schur power estimates. -/
theorem schurGap_raw_lintegral_eq_normalized
    (n y : ℝ) (hn : 0 < n) (hy : 0 < y)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(n/2)*s)) *
      ENNReal.ofReal ((Real.sqrt (s+4*y^2))⁻¹) * g s) =
        ((ENNReal.ofReal (n/2))⁻¹ * schurGapKernelNormalizer n y) *
          ∫⁻ s, g s ∂schurSquaredGapLaw n y := by
  have hn0 : ENNReal.ofReal (n/2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hZ0 : schurGapKernelNormalizer n y ≠ 0 := by
    rw [schurGapKernelNormalizer_eq_ofReal n y hn hy]
    exact (ENNReal.ofReal_pos.mpr (schurGapWeight_normalizer_pos n y hn hy)).ne'
  have hZtop : schurGapKernelNormalizer n y ≠ ∞ := by
    rw [schurGapKernelNormalizer_eq_ofReal n y hn hy]
    exact ENNReal.ofReal_ne_top
  rw [schurSquaredGapLaw_lintegral_kernel n y hn hy g hg]
  let a := ENNReal.ofReal (n/2)
  let Z := schurGapKernelNormalizer n y
  let R := ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(n/2)*s)) *
    ENNReal.ofReal ((Real.sqrt (s+4*y^2))⁻¹) * g s
  change R = (a⁻¹*Z)*((a*Z⁻¹)*R)
  calc
    R = ((a⁻¹*a)*(Z*Z⁻¹))*R := by
      rw [ENNReal.inv_mul_cancel hn0 ENNReal.ofReal_ne_top,
        ENNReal.mul_inv_cancel hZ0 hZtop,one_mul,one_mul]
    _ = _ := by ac_rfl

#print axioms schurGapExplicitDensity_measurable
#print axioms schurSquaredGapLaw_lintegral_kernel
#print axioms schurGap_raw_lintegral_eq_normalized
end SpectralRadiusUpperTail
