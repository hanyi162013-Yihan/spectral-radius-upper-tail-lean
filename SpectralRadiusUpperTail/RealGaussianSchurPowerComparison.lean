import SpectralRadiusUpperTail.RealSchurConditionalPowerBound
import SpectralRadiusUpperTail.RealGaussianSchurIntegralBound
import SpectralRadiusUpperTail.RealGaussianSchurMomentIntegrability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology

/-- The actual real Gaussian Hilbert--Schmidt power moment is bounded by
the buffered spectral-radius moment with an arbitrarily small exponential
loss. The Schur conditional distribution is derived from the matrix law. -/
theorem realGaussian_schur_power_comparison : GaussianSchurPowerComparisonInput := by
  intro α hα η hη ε hε
  have hratio := floor_linear_power_ratio α hα
  have hconditional := realSchurConditionalNative_power_subexponential
    (fun n => ⌊α*(n : ℝ)⌋₊) α η ε hη hε hratio
  filter_upwards [hconditional,floor_linear_power_eventually_pos α hα,
    eventually_gt_atTop 0] with n hcond hk hn
  have hh := realGaussian_power_lintegral_le_of_conditional n ⌊α*(n : ℝ)⌋₊ hk η
    (Real.exp ((n : ℝ)*ε)) (by
      intro I x u hu
      have hm : I.1.blockCount ≤ n := Nat.le_of_lt_succ I.1.val.1.isLt
      exact hcond I.1.blockCount I.1.sizes I.1.sizes_small hm hk x u hu)
  rw [← gaussianPowerMoment_ofReal_eq_lintegral,
    ← realGaussianShiftedRadiusPower_ofReal_integral n _ hn η hη.le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le
    (integral_nonneg (realGaussianShiftedRadiusPower_nonneg n _ η hη.le)))).mp hh

#print axioms realGaussian_schur_power_comparison
end SpectralRadiusUpperTail
