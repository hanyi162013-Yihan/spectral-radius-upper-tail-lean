import SpectralRadiusUpperTail.RealGammaShiftProduct
import SpectralRadiusUpperTail.RealGinibreWeightedCoreIntegral
import SpectralRadiusUpperTail.RealGinibreWeightedUpperExponent
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The exact uncut positive real one-point factor has the shifted-Gamma
exponential envelope used by the power-moment rate calculation. -/
theorem realGinibreCoreDensity_weighted_upper (n k : ℕ) (hn : 0 < n) :
    (∫ x in Set.Ioi (0 : ℝ), x^(2*k) * realGinibreCoreDensity n x) ≤
      Real.exp (realGinibreWeightedUpperExponent n k) := by
  let b : ℝ := (n : ℝ)/2
  have hb : 0 < b := by dsimp [b]; positivity
  have hnum : 0 < Real.Gamma (b+(k : ℝ)+1) := by
    apply Real.Gamma_pos_of_pos
    positivity
  have hden : 0 < Real.Gamma (b+1) := by
    apply Real.Gamma_pos_of_pos
    positivity
  have hfactor : 0 ≤ (1/2 : ℝ)*b^(-(k : ℝ)) := by positivity
  have hshift := mul_le_mul_of_nonneg_left
    (real_gamma_ratio_le_shifted b hb k) hfactor
  have hlog :
      Real.log ((1/2)*b^(-(k : ℝ)) *
        (Real.Gamma (b+(k : ℝ)+1)/Real.Gamma (b+1))) =
      realGinibreWeightedUpperExponent n k := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0)
        (by positivity : b^(-(k : ℝ)) ≠ 0),
      Real.log_rpow hb,
      Real.log_div hnum.ne' hden.ne',
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [Real.log_one, zero_sub]
    unfold realGinibreWeightedUpperExponent
    dsimp [b]
    ring
  have harg : 0 < (1/2)*b^(-(k : ℝ)) *
      (Real.Gamma (b+(k : ℝ)+1)/Real.Gamma (b+1)) := by positivity
  have hexp : Real.exp (realGinibreWeightedUpperExponent n k) =
      (1/2)*b^(-(k : ℝ)) *
        (Real.Gamma (b+(k : ℝ)+1)/Real.Gamma (b+1)) := by
    rw [← hlog, Real.exp_log harg]
  rw [realGinibreCoreDensity_weighted_integral_ratio n k hn, hexp]
  change (1/2)*b^(-(k : ℝ)) *
      (Real.Gamma (b+(k : ℝ))/Real.Gamma b) ≤
    (1/2)*b^(-(k : ℝ)) *
      (Real.Gamma (b+(k : ℝ)+1)/Real.Gamma (b+1))
  exact hshift

/-- A linear power of the uncut real one-point factor has precisely the
candidate speed-`n` upper exponent, up to any prescribed positive error. -/
theorem realGinibreCoreDensity_weighted_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x in Set.Ioi (0 : ℝ),
        x^(2*k n) * realGinibreCoreDensity n x) ≤
          Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  filter_upwards [eventually_gt_atTop 0,
    realGinibreWeightedUpperExponent_eventual k α hα hk δ hδ]
    with n hn hupper
  exact (realGinibreCoreDensity_weighted_upper n (k n) hn).trans hupper

#print axioms realGinibreCoreDensity_weighted_upper
#print axioms realGinibreCoreDensity_weighted_upper_eventual
end SpectralRadiusUpperTail
