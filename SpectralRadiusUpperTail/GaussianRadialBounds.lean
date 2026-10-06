import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SpectralRadiusUpperTail

/-- Every even radial power times a Gaussian has an explicit global bound. -/
lemma gaussian_radial_even_bound (a r : ℝ) (ha : 0 < a) (n : ℕ) :
    r^(2*n)*Real.exp (-r^2/a) ≤ (n.factorial : ℝ)*a^n := by
  have hu : 0 ≤ r^2/a := by positivity
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have ht := Real.pow_div_factorial_le_exp (r^2/a) hu n
  have hh := (div_le_iff₀ hfac).mp ht
  have hp : r^(2*n) ≤ (Real.exp (r^2/a)*(n.factorial : ℝ))*a^n := by
    apply (div_le_iff₀ (pow_pos ha n)).mp
    simpa only [div_pow, ← pow_mul] using hh
  calc
    _ ≤ ((Real.exp (r^2/a)*(n.factorial : ℝ))*a^n)*Real.exp (-r^2/a) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = ((n.factorial : ℝ)*a^n)*(Real.exp (r^2/a)*Real.exp (-(r^2/a))) := by ring
    _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

lemma gaussian_radial_odd_bounds (a r : ℝ) (ha : 0 < a) :
    r*Real.exp (-r^2/a) ≤ 1+a ∧
      r^3*Real.exp (-r^2/a) ≤ 1+2*a^2 := by
  have h0 : Real.exp (-r^2/a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le)
  have h2 : r^2*Real.exp (-r^2/a) ≤ a := by
    simpa using gaussian_radial_even_bound a r ha 1
  have h4 : r^4*Real.exp (-r^2/a) ≤ 2*a^2 := by
    simpa [Nat.factorial] using gaussian_radial_even_bound a r ha 2
  have hr : r ≤ 1+r^2 := by nlinarith [sq_nonneg (r-1)]
  have hr3 : r^3 ≤ 1+r^4 := by
    nlinarith [sq_nonneg (r^2-r), sq_nonneg (r^2-1), sq_nonneg (r^2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_right hr (Real.exp_nonneg (-r^2/a))
    nlinarith only [hh, h0, h2]
  · have hh := mul_le_mul_of_nonneg_right hr3 (Real.exp_nonneg (-r^2/a))
    nlinarith only [hh, h0, h4]

#print axioms gaussian_radial_even_bound
#print axioms gaussian_radial_odd_bounds
end SpectralRadiusUpperTail
