import SpectralRadiusUpperTail.RealGaussianPowerSingleBoundary
import SpectralRadiusUpperTail.PolynomialExponentialBudget

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- A linear loss in the nonreal one-point bound is subexponential and
does not change the sharp power-moment exponent. -/
theorem realGaussianNonrealPower_upper_of_linear_weighted
    (C : ℝ) (hC : 0 < C)
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) ≤
        C*(n : ℝ)*(∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      2*(∫ a, realGaussianUpperNonrealExteriorPower n (k n) a ∂gaussianMatrixLaw n) ≤
        Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  have hh : 0 < δ/2 := by linarith
  filter_upwards [eventually_ge_atTop 3,
    eventually_positive_polynomial_le_exp C hC 1 (δ/2) hh,
    realGinibreNonrealDensityAt_weighted_upper_eventual k α hα hk (δ/2) hh]
    with n hn hpoly hrate
  simp only [pow_one] at hpoly
  calc
    _ ≤ C*(n : ℝ)*(∫ z : ℂ in {z | 1 < ‖z‖},
        ‖z‖^(2*k n)*realGinibreNonrealDensityAt n z) := hUpper n (k n) hn
    _ ≤ C*(n : ℝ)*Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) :=
      mul_le_mul_of_nonneg_left hrate (mul_nonneg hC.le (Nat.cast_nonneg n))
    _ ≤ Real.exp ((n : ℝ)*(δ/2))*Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem realGaussianClippedRadiusPower_upper_of_linear_nonreal
    (C : ℝ) (hC : 0 < C)
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) ≤
        C*(n : ℝ)*(∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ a, realGaussianClippedRadiusPower n (k n) a ∂gaussianMatrixLaw n) ≤
        Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  have hh : 0 < δ/2 := by linarith
  filter_upwards [eventually_ge_atTop 3,
    realGaussianPositivePower_upper_eventual k α hα hk (δ/2) hh,
    realGaussianNonrealPower_upper_of_linear_weighted C hC hUpper k α hα hk (δ/2) hh,
    eventually_exp_prefactor_absorb 4 (powerRate 1 α+δ/2) (δ/2) (by norm_num) hh]
    with n hn hp hc ha
  have hone : 1 ≤ Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) := by
    have hz : 0 ≤ (n : ℝ)*(powerRate 1 α+δ/2) :=
      mul_nonneg (Nat.cast_nonneg n) (add_nonneg (powerRate_one_nonneg α hα.le) hh.le)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hz
  calc
    _ ≤ 1+(∫ a, realGaussianExteriorRootPower n (k n) a ∂gaussianMatrixLaw n) :=
      realGaussianClippedRadiusPower_integral_le_rootPower n (k n) (by omega)
        (realGaussianExteriorRootPower_integrable n (k n) (by omega))
    _ = 1+(2*(∫ a, realGaussianPositiveRealExteriorPower n (k n) a ∂gaussianMatrixLaw n)+
        2*(∫ a, realGaussianUpperNonrealExteriorPower n (k n) a ∂gaussianMatrixLaw n)) := by
      rw [realGaussianExteriorRootPower_mean_partition n (k n) (by omega)]
    _ ≤ 4*Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) := by linarith
    _ ≤ Real.exp ((n : ℝ)*(powerRate 1 α+δ/2+δ/2)) := ha
    _ = _ := by congr 1; ring

theorem gaussianPowerUpperInput_of_linear_nonreal_weighted
    (C : ℝ) (hC : 0 < C)
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) ≤
        C*(n : ℝ)*(∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z)) : GaussianPowerUpperInput := by
  apply gaussianPowerUpperInput_of_radiusMoment_and_schur ?_ realGaussian_schur_power_comparison
  apply gaussianRadiusMomentUpperInput_of_clipped
  intro α hα δ hδ
  exact realGaussianClippedRadiusPower_upper_of_linear_nonreal C hC hUpper
    (fun n => ⌊α*(n : ℝ)⌋₊) α hα (floor_linear_power_ratio α hα) δ hδ

#print axioms realGaussianNonrealPower_upper_of_linear_weighted
#print axioms realGaussianClippedRadiusPower_upper_of_linear_nonreal
#print axioms gaussianPowerUpperInput_of_linear_nonreal_weighted
end SpectralRadiusUpperTail
