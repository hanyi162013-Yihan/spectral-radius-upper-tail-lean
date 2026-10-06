import SpectralRadiusUpperTail.RealGaussianRootPowerIntegrable
import SpectralRadiusUpperTail.RealGaussianSchurPowerConditional

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem realGaussianShiftedRadiusPower_nonneg (n k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (x : (Fin n × Fin n) → ℝ) : 0 ≤ realGaussianShiftedRadiusPower n k η x := by
  unfold realGaussianShiftedRadiusPower
  apply pow_nonneg
  exact add_nonneg (le_trans (by norm_num) (le_max_left _ _)) hη

theorem realGaussianShiftedRadiusPower_integrable (n k : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 ≤ η) :
    Integrable (realGaussianShiftedRadiusPower n k η) (gaussianMatrixLaw n) := by
  have hc := realGaussianClippedRadiusPower_integrable n k hn
    (realGaussianExteriorRootPower_integrable n k hn)
  have henv := hc.const_mul ((1+η)^(2*k))
  exact henv.mono_nonneg (realGaussianShiftedRadiusPower_measurable n k η).aestronglyMeasurable
    (Filter.Eventually.of_forall (realGaussianShiftedRadiusPower_nonneg n k η hη))
    (Filter.Eventually.of_forall (realGaussianShiftedRadiusPower_le_clipped n k η hη))

theorem gaussianPowerMoment_ofReal_eq_lintegral (n k : ℕ) :
    ENNReal.ofReal (gaussianPowerMoment n k)=
      ∫⁻ x, ENNReal.ofReal (scaledFrobeniusPowerSquared (1/Real.sqrt n) k x) ∂gaussianMatrixLaw n := by
  have hi : Integrable (scaledFrobeniusPowerSquared (1/Real.sqrt n) k) (gaussianMatrixLaw n) :=
    product_scaledFrobeniusPowerSquared_integrable (fun _ => standardNormal)
      (fun _ j => standardNormal_pow_integrable j) _ k
  exact ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (scaledFrobeniusPowerSquared_nonneg _ k))

theorem realGaussianShiftedRadiusPower_ofReal_integral (n k : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 ≤ η) :
    ENNReal.ofReal (∫ x, realGaussianShiftedRadiusPower n k η x ∂gaussianMatrixLaw n)=
      ∫⁻ x, ENNReal.ofReal (realGaussianShiftedRadiusPower n k η x) ∂gaussianMatrixLaw n :=
  ofReal_integral_eq_lintegral_ofReal (realGaussianShiftedRadiusPower_integrable n k hn η hη)
    (Filter.Eventually.of_forall (realGaussianShiftedRadiusPower_nonneg n k η hη))

#print axioms realGaussianShiftedRadiusPower_integrable
#print axioms gaussianPowerMoment_ofReal_eq_lintegral
#print axioms realGaussianShiftedRadiusPower_ofReal_integral
end SpectralRadiusUpperTail
