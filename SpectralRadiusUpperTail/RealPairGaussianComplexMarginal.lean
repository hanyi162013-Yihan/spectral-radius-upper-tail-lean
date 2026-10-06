import SpectralRadiusUpperTail.RealPairGaussianSpectralMarginal
import SpectralRadiusUpperTail.PositiveSquareLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem realPairGap_erfc_jacobian (y : ℝ) (hy : 0 < y) :
    ENNReal.ofReal (2*y)*((ENNReal.ofReal (1/2 : ℝ))⁻¹*schurGapKernelNormalizer 1 y)=
      2*ENNReal.ofReal (gaussianErfcCorrection (Real.sqrt 2*y)) := by
  rw [schurGapKernelNormalizer_eq_erfcCorrection 1 y (by norm_num) hy]
  norm_num only [mul_one]
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < 2*y)]
  have hi : (ENNReal.ofReal (1/2 : ℝ))⁻¹=(2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    norm_num
  rw [hi,div_eq_mul_inv]
  calc
    _ = (2*ENNReal.ofReal (gaussianErfcCorrection (Real.sqrt 2*y)))*
        (ENNReal.ofReal (2*y)*(ENNReal.ofReal (2*y))⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < 2*y)).ne' ENNReal.ofReal_ne_top,mul_one]

/-- Explicit Gaussian marginal of a nonreal two-by-two block, with the
ordinary positive imaginary coordinate and the erfc correction exposed. -/
theorem realPairGaussian_complex_marginal
    (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ B in realPairNonrealEntrySet, realPairGaussianWeight 1 B*
      H (realPairCenter (Matrix.of B.curry),realPairHeightSq (Matrix.of B.curry))) =
      ENNReal.ofReal (4*Real.pi)*
        ∫⁻ x : ℝ, ∫⁻ y in Set.Ioi (0 : ℝ),
          (ENNReal.ofReal (Real.exp (-(x^2+y^2)))*
            ENNReal.ofReal (gaussianErfcCorrection (Real.sqrt 2*y)))*H (x,y^2) := by
  rw [realPairGaussian_spectral_marginal 1 (by norm_num) H hH]
  have hinner (x : ℝ) :
      (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-1*(x^2+u)))*
        (((ENNReal.ofReal (1/2 : ℝ))⁻¹*schurGapKernelNormalizer 1 (Real.sqrt u))*H (x,u))) =
      2*∫⁻ y in Set.Ioi (0 : ℝ),
        (ENNReal.ofReal (Real.exp (-(x^2+y^2)))*
          ENNReal.ofReal (gaussianErfcCorrection (Real.sqrt 2*y)))*H (x,y^2) := by
    rw [positive_square_lintegral,← lintegral_const_mul' 2 _ (by norm_num)]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change 0 < y at hy
    dsimp only
    rw [Real.sqrt_sq hy.le,neg_one_mul]
    calc
      _ = (ENNReal.ofReal (2*y)*((ENNReal.ofReal (1/2 : ℝ))⁻¹*
          schurGapKernelNormalizer 1 y))*
          (ENNReal.ofReal (Real.exp (-(x^2+y^2)))*H (x,y^2)) := by ac_rfl
      _ = _ := by rw [realPairGap_erfc_jacobian y hy]; ac_rfl
  simp_rw [hinner]
  rw [lintegral_const_mul' 2 _ (by norm_num),← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  ring

#print axioms realPairGap_erfc_jacobian
#print axioms realPairGaussian_complex_marginal
end SpectralRadiusUpperTail
