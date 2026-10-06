import SpectralRadiusUpperTail.RealGaussianPositivePowerRate
import SpectralRadiusUpperTail.RealGaussianRootPowerMeanPartition
import SpectralRadiusUpperTail.RealGaussianRadiusMomentFromClipped

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Only the nonreal weighted one-point upper bound is assumed here.
The actual real-root weighted formula and its sharp rate are proved. -/
theorem realGaussianClippedRadiusPower_upper_of_nonreal_weighted
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ a, realGaussianClippedRadiusPower n (k n) a ∂gaussianMatrixLaw n) ≤
        Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  have hhalf : 0 < δ/2 := by linarith
  filter_upwards [eventually_ge_atTop 3,
    realGaussianPositivePower_upper_eventual k α hα hk (δ/2) hhalf,
    realGinibreNonrealDensityAt_weighted_upper_eventual k α hα hk (δ/2) hhalf,
    eventually_exp_prefactor_absorb 4 (powerRate 1 α+δ/2) (δ/2)
      (by norm_num) hhalf] with n hn hp hc ha
  have hnon := (hUpper n (k n) hn).trans hc
  have hone : 1 ≤ Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) := by
    have harg : 0 ≤ (n : ℝ)*(powerRate 1 α+δ/2) := mul_nonneg (Nat.cast_nonneg n)
      (add_nonneg (powerRate_one_nonneg α hα.le) hhalf.le)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr harg
  calc
    _ ≤ 1+(∫ a, realGaussianExteriorRootPower n (k n) a ∂gaussianMatrixLaw n) :=
      realGaussianClippedRadiusPower_integral_le_rootPower n (k n) (by omega)
        (realGaussianExteriorRootPower_integrable n (k n) (by omega))
    _ = 1+(2*(∫ a, realGaussianPositiveRealExteriorPower n (k n) a ∂gaussianMatrixLaw n) +
        2*(∫ a, realGaussianUpperNonrealExteriorPower n (k n) a ∂gaussianMatrixLaw n)) := by
      rw [realGaussianExteriorRootPower_mean_partition n (k n) (by omega)]
    _ ≤ 4*Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) := by linarith
    _ ≤ Real.exp ((n : ℝ)*(powerRate 1 α+δ/2+δ/2)) := ha
    _ = _ := by congr 1; ring

/-- The real-root intensity is no longer an external assumption in the
main Gaussian power interface. The remaining inputs are the actual
nonreal weighted count bound and the actual conditional Schur comparison. -/
theorem gaussianPowerUpperInput_of_nonreal_weighted_and_schur
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (hSchur : GaussianSchurPowerComparisonInput) :
    GaussianPowerUpperInput := by
  apply gaussianPowerUpperInput_of_radiusMoment_and_schur ?_ hSchur
  apply gaussianRadiusMomentUpperInput_of_clipped
  intro α hα δ hδ
  exact realGaussianClippedRadiusPower_upper_of_nonreal_weighted hUpper
    (fun n => ⌊α*(n : ℝ)⌋₊) α hα (floor_linear_power_ratio α hα) δ hδ

#print axioms realGaussianClippedRadiusPower_upper_of_nonreal_weighted
#print axioms gaussianPowerUpperInput_of_nonreal_weighted_and_schur
end SpectralRadiusUpperTail
