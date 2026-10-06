import SpectralRadiusUpperTail.RealGinibreNonrealDensityAt
import SpectralRadiusUpperTail.RealGinibreFirstCoreCompare
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The nonreal one-point expression is uniformly controlled outside the
unit disk by the same uncut real-Ginibre Gamma factor. -/
theorem realGinibreNonrealDensityAt_le_exp_core_of_budget
    (n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hbudget : Real.log (n : ℝ)-
        Real.log (realGinibreCoreDensity n 1)+1/2 ≤ (n : ℝ)*ε)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    realGinibreNonrealDensityAt n z ≤
      Real.exp ((n : ℝ)*ε)*realGinibreCoreDensity n ‖z‖ := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hfrac : (n : ℝ)/Real.pi ≤ (n : ℝ) := by
    apply (div_le_iff₀ hpi0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpi hnR]
  have hbound := (realGinibreNonrealDensityAt_bound n z hz).2
  have hcoef := mul_le_mul_of_nonneg_right hfrac
    (Real.exp_pos (-(n : ℝ)*rate 2 ‖z‖)).le
  have hcore := realGinibrePoissonEnvelope_le_exp_core_of_budget
    n hn ε hbudget ‖z‖ hz
  exact hbound.trans (hcoef.trans hcore)

#print axioms realGinibreNonrealDensityAt_le_exp_core_of_budget
end SpectralRadiusUpperTail
