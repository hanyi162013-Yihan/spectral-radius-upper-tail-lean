import SpectralRadiusUpperTail.RealGinibreFirstTailUpper
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- A fixed prefactor version of the faster finite-Poisson real
one-point tail bound. -/
theorem realGinibreFirstTailSimpleUpper (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 < r) :
    (∫ x : ℝ in Ioi r, realGinibreFirstDensity n x) ≤
      (1/(2*(r-1/r))) * Real.exp (-(n : ℝ)*rate 2 r) := by
  have hrpos : 0 < r := by linarith
  have hc : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 1 ≤ 2*Real.pi := by nlinarith [Real.pi_gt_three]
  have hden : 0 < 2*Real.pi := by positivity
  have hfrac : (n : ℝ)/(2*Real.pi) ≤ (n : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpi hnR.le]
  have hsqrt : Real.sqrt ((n : ℝ)/(2*Real.pi)) ≤ (n : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hnR.le
    · exact hfrac.trans (by nlinarith [hnOne])
  have hbase := realGinibreFirstTailUpper n hn r hr
  calc
    _ ≤ (Real.sqrt ((n : ℝ)/(2*Real.pi)) *
          Real.exp (-(n : ℝ)*rate 2 r)) /
          (2*(n : ℝ)*(r-1/r)) := hbase
    _ ≤ ((n : ℝ)*Real.exp (-(n : ℝ)*rate 2 r)) /
          (2*(n : ℝ)*(r-1/r)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le)
        (by positivity)
    _ = _ := by
      field_simp [hnR.ne', ne_of_gt hc]

#print axioms realGinibreFirstTailSimpleUpper
end SpectralRadiusUpperTail
