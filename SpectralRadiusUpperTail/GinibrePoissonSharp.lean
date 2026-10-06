import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The finite exponential sum occurring in both real and complex Ginibre
one-point formulas. The correlation formula itself is not assumed here. -/
noncomputable def ginibreExpPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x^k/(Nat.factorial k : ℝ)

/-- Exponential tilting gives a sharp finite-dimensional Poisson bound. -/
theorem ginibreExpPartial_le_tilt (n : ℕ) {x a : ℝ}
    (hx : 0 ≤ x) (ha : 1 ≤ a) :
    ginibreExpPartial n x ≤ a^n * Real.exp (x/a) := by
  have hapos : 0 < a := by linarith
  have hterm (k : ℕ) (hk : k ∈ Finset.range n) :
      x^k/(Nat.factorial k : ℝ) ≤
        a^n*((x/a)^k/(Nat.factorial k : ℝ)) := by
    have hid : x^k = a^k*(x/a)^k := by
      rw [← mul_pow, mul_div_cancel₀ x hapos.ne']
    rw [hid, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ ha (Finset.mem_range.mp hk).le) (by positivity)
  calc
    ginibreExpPartial n x ≤
        ∑ k ∈ Finset.range n, a^n*((x/a)^k/(Nat.factorial k : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = a^n * ginibreExpPartial n (x/a) := by
      simp only [ginibreExpPartial, Finset.mul_sum]
    _ ≤ a^n * Real.exp (x/a) :=
      mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (div_nonneg hx hapos.le) n)
        (by positivity)

/-- At `x=n u`, the tilt `a=u` yields the full Poisson Cramér exponent.
This is the analytic part reused from the earlier complex-Ginibre work. -/
theorem ginibrePoissonCutoff_sharp (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    Real.exp (-(n : ℝ)*u) * ginibreExpPartial n ((n : ℝ)*u) ≤
      Real.exp ((n : ℝ)*(1+Real.log u-u)) := by
  have hupos : 0 < u := by linarith
  have ht := ginibreExpPartial_le_tilt n
    (x := (n : ℝ)*u) (a := u) (by positivity) hu
  have he : (n : ℝ)*u/u = (n : ℝ) := mul_div_cancel_right₀ _ hupos.ne'
  have hpow : u^n = Real.exp ((n : ℝ)*Real.log u) := by
    simpa only [Real.exp_log hupos] using
      (Real.exp_nat_mul (Real.log u) n).symm
  rw [he] at ht
  calc
    _ ≤ Real.exp (-(n : ℝ)*u) * (u^n * Real.exp (n : ℝ)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = _ := by
      rw [hpow]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

#print axioms ginibreExpPartial_le_tilt
#print axioms ginibrePoissonCutoff_sharp
end SpectralRadiusUpperTail
