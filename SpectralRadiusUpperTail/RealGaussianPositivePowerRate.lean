import SpectralRadiusUpperTail.RealGaussianPositivePowerFormula
import SpectralRadiusUpperTail.GaussianMarkedRealWeightedBudget
import SpectralRadiusUpperTail.RealGaussianWeightedSignSymmetry

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Unconditional sharp exponential upper bound for the actual positive
real-root power statistic, with degree growing linearly in dimension. -/
theorem realGaussianPositivePower_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ a, realGaussianPositiveRealExteriorPower n (k n) a
        ∂gaussianMatrixLaw n) ≤
          Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  filter_upwards [eventually_ge_atTop 2,
    gaussianMarkedRealDensity_weighted_upper_eventual k α hα hk δ hδ]
    with n hn hscalar
  rwa [realGaussianPositivePower_eq_weighted_density n (k n) hn]

theorem realGaussianNegativePower_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ a, realGaussianNegativeRealExteriorPower n (k n) a
        ∂gaussianMatrixLaw n) ≤
          Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  filter_upwards [eventually_gt_atTop 0,
    realGaussianPositivePower_upper_eventual k α hα hk δ hδ]
    with n hn hp
  rwa [realGaussianWeightedRealHalflines_equal n (k n)
    (realGaussianPositiveRealExteriorPower_integrable n (k n) hn)]

#print axioms realGaussianPositivePower_upper_eventual
#print axioms realGaussianNegativePower_upper_eventual
end SpectralRadiusUpperTail
