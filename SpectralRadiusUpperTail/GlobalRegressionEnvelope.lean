import SpectralRadiusUpperTail.DensityCost
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SpectralRadiusUpperTail

/-- A global conditional mean bound gives a squared regression remainder with
an exponential coefficient proportional to the current coefficient energy. -/
theorem global_regression_square_bound {𝕂 : Type*} [RCLike 𝕂]
    (m b s : 𝕂) (t D A B : ℝ) (ht : 0 < t) (hD : t ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : ‖m‖ ≤ A*(‖b‖*(1+‖s‖))*Real.exp (B*(‖b‖*(1+‖s‖))^2)) :
    ‖m-(1/D : ℝ) • (star b*s)‖^2 ≤
      (4*(A^2+1/t^2))*‖b‖^2*(1+‖s‖^2)*
        Real.exp ((4*B)*‖b‖^2*(1+‖s‖^2)) := by
  let u := ‖b‖*(1+‖s‖)
  let V := ‖b‖^2*(1+‖s‖^2)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hDp : 0 < D := ht.trans_le hD
  have hg : ‖(1/D : ℝ) • (star b*s)‖ ≤ u/t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hDp), norm_mul, norm_star]
    calc
      _ = (‖b‖*‖s‖)/D := by ring
      _ ≤ u/t := div_le_div₀ (by positivity) (by dsimp [u]; nlinarith [norm_nonneg b]) ht hD
  have huV : u^2 ≤ 2*V := by
    have hs : (1+‖s‖)^2 ≤ 2*(1+‖s‖^2) := by nlinarith [sq_nonneg (‖s‖-1)]
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖b‖)
    dsimp [u, V]
    nlinarith only [hh]
  have hm2 : ‖m‖^2 ≤ A^2*u^2*Real.exp (2*B*u^2) := by
    have hs := mul_self_le_mul_self (norm_nonneg m) hm
    have heq : (Real.exp (B*u^2))^2 = Real.exp (2*B*u^2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (A*u*Real.exp (B*u^2))^2 := by simpa only [pow_two] using hs
      _ = _ := by rw [mul_pow, mul_pow, heq]
  have hg2 : ‖(1/D : ℝ) • (star b*s)‖^2 ≤ u^2/t^2 := by
    have hs := mul_self_le_mul_self (norm_nonneg _) hg
    simpa only [← pow_two, div_pow] using hs
  have he1 : 1 ≤ Real.exp (2*B*u^2) := Real.one_le_exp_iff.mpr (by positivity)
  have heV : Real.exp (2*B*u^2) ≤ Real.exp (4*B*V) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left huV (show 0 ≤ 2*B by positivity)
    nlinarith only [hh]
  have hcoef : 0 ≤ 2*(A^2+1/t^2) := by positivity
  calc
    _ ≤ 2*‖m‖^2+2*‖(1/D : ℝ) • (star b*s)‖^2 := by
      simpa only [mul_add] using norm_sub_sq_le_twice m ((1/D : ℝ) • (star b*s))
    _ ≤ 2*(A^2*u^2*Real.exp (2*B*u^2))+2*(u^2/t^2) := by linarith only [hm2, hg2]
    _ ≤ (2*(A^2+1/t^2))*u^2*Real.exp (2*B*u^2) := by
      have hh := mul_le_mul_of_nonneg_left he1 (show 0 ≤ 2*(u^2/t^2) by positivity)
      calc
        _ ≤ 2*(A^2*u^2*Real.exp (2*B*u^2))+2*(u^2/t^2)*Real.exp (2*B*u^2) :=
          add_le_add le_rfl (by simpa only [mul_one] using hh)
        _ = _ := by ring
    _ ≤ (2*(A^2+1/t^2))*(2*V)*Real.exp (4*B*V) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left huV hcoef) heV (Real.exp_nonneg _)
        (mul_nonneg hcoef (by positivity))
    _ = _ := by
      have heq : 4*B*V = (4*B)*‖b‖^2*(1+‖s‖^2) := by dsimp [V]; ring
      rw [heq]
      dsimp [V]
      ring

#print axioms global_regression_square_bound
end SpectralRadiusUpperTail
