import SpectralRadiusUpperTail.RealGaussianWeightedRadiusInterface
import SpectralRadiusUpperTail.PowerRatePositive
import SpectralRadiusUpperTail.ExponentialPrefactorBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The explicit weighted one-point formulas imply the candidate
linear-power bound for the actual normalized real Gaussian spectral radius.
The expectation identity for characteristic-polynomial roots is stated as
the finite-dimensional input; no Gaussian radius LDP is imported. -/
theorem realGaussianClippedRadiusPower_upper_of_onePoint
    (hroot : ∀ n k, 3 ≤ n →
      Integrable (realGaussianExteriorRootPower n k)
        (gaussianMatrixLaw n))
    (hidentity : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianExteriorRootPower n k x
        ∂gaussianMatrixLaw n) ≤
          realGinibreWeightedOnePointEnvelope n k)
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x, realGaussianClippedRadiusPower n (k n) x
        ∂gaussianMatrixLaw n) ≤
          Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  let ε : ℝ := δ/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hrate : 0 ≤ powerRate 1 α :=
    powerRate_one_nonneg α hα.le
  filter_upwards [eventually_ge_atTop 3,
    realGinibreWeightedOnePointEnvelope_upper_eventual k α hα hk ε hε,
    eventually_exp_prefactor_absorb 2 (powerRate 1 α+ε) ε
      (by norm_num) hε] with n hn hscalar habsorb
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnpos : 0 < n := by omega
  have hE : 1 ≤ Real.exp ((n : ℝ)*(powerRate 1 α+ε)) := by
    have harg : 0 ≤ (n : ℝ)*(powerRate 1 α+ε) :=
      mul_nonneg hnR (by linarith)
    simpa only [← Real.exp_zero] using Real.exp_le_exp.mpr harg
  calc
    (∫ x, realGaussianClippedRadiusPower n (k n) x
      ∂gaussianMatrixLaw n) ≤
        1+realGinibreWeightedOnePointEnvelope n (k n) :=
      realGaussianClippedRadiusPower_integral_le_onePointEnvelope
        n (k n) hnpos (hroot n (k n) hn) (hidentity n (k n) hn)
    _ ≤ 1+Real.exp ((n : ℝ)*(powerRate 1 α+ε)) :=
      add_le_add_right hscalar 1
    _ ≤ 2*Real.exp ((n : ℝ)*(powerRate 1 α+ε)) := by linarith
    _ ≤ Real.exp ((n : ℝ)*(powerRate 1 α+ε+ε)) := habsorb
    _ = _ := by congr 1; dsimp [ε]; ring

#print axioms realGaussianClippedRadiusPower_upper_of_onePoint
end SpectralRadiusUpperTail
