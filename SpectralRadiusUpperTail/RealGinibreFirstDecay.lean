import SpectralRadiusUpperTail.RealGinibreFirstDensity
import SpectralRadiusUpperTail.RateTwoTailSlope
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The finite-Poisson part of the real one-point formula has the faster
complex-rate exponential envelope beyond a fixed radius. -/
theorem realGinibreFirstDensity_decay (n : ℕ) (hn : 1 ≤ n)
    (r x : ℝ) (hr : 1 < r) (hrx : r ≤ x) :
    realGinibreFirstDensity n x ≤
      (Real.sqrt ((n : ℝ)/(2*Real.pi)) *
        Real.exp (-(n : ℝ)*rate 2 r)) *
        Real.exp (-(2*(n : ℝ)*(r-1/r))*(x-r)) := by
  have hx1 : 1 ≤ x := (le_of_lt hr).trans hrx
  have hpoint := (realGinibreFirstDensity_bound n hn x hx1).2
  have hslope := rate_two_tail_slope r x hr hrx
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have harg : -(n : ℝ)*rate 2 x ≤
      -(n : ℝ)*rate 2 r - (2*(n : ℝ)*(r-1/r))*(x-r) := by
    have hm := mul_le_mul_of_nonneg_left hslope hnR
    nlinarith [hm]
  have hexp := Real.exp_le_exp.mpr harg
  calc
    realGinibreFirstDensity n x ≤
        Real.sqrt ((n : ℝ)/(2*Real.pi)) *
          Real.exp (-(n : ℝ)*rate 2 x) := hpoint
    _ ≤ Real.sqrt ((n : ℝ)/(2*Real.pi)) *
          Real.exp (-(n : ℝ)*rate 2 r -
            (2*(n : ℝ)*(r-1/r))*(x-r)) :=
      mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

#print axioms realGinibreFirstDensity_decay
end SpectralRadiusUpperTail
