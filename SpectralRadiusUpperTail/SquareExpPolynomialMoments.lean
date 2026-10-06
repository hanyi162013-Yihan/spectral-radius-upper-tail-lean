import SpectralRadiusUpperTail.GaussianRadialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma norm_pow_squareExp_bound (c r : ℝ) (hc : 0 < c) (n : ℕ) :
    r^n ≤ (1+(n.factorial : ℝ)*(1/c)^n)*Real.exp (c*r^2) := by
  have heq : -r^2/(1/c) = -(c*r^2) := by field_simp
  have hr := gaussian_radial_even_bound (1/c) r (by positivity) n
  rw [heq] at hr
  have h0 : Real.exp (-(c*r^2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
  have hp : r^n ≤ 1+r^(2*n) := by
    have hh : r^n ≤ 1+(r^n)^2 := by nlinarith [sq_nonneg (r^n-1)]
    simpa only [← pow_mul, Nat.mul_comm n 2] using hh
  have hb : r^n*Real.exp (-(c*r^2)) ≤ 1+(n.factorial : ℝ)*(1/c)^n := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (-(c*r^2)))
    nlinarith only [hh, h0, hr]
  calc
    _ = (r^n*Real.exp (-(c*r^2)))*Real.exp (c*r^2) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)

/-- The original square-exponential assumption supplies every finite absolute
moment, including the third moment used in Gaussian replacement. -/
theorem squareExp_norm_pow_integrable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (c : ℝ) (hc : 0 < c)
    (he : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ) (n : ℕ) :
    Integrable (fun x : E => ‖x‖^n) μ := by
  apply (he.const_mul (1+(n.factorial : ℝ)*(1/c)^n)).mono_nonneg (by fun_prop)
    (Filter.Eventually.of_forall (fun x => pow_nonneg (norm_nonneg x) n))
  exact Filter.Eventually.of_forall (fun x => norm_pow_squareExp_bound c ‖x‖ hc n)

#print axioms squareExp_norm_pow_integrable
end SpectralRadiusUpperTail
