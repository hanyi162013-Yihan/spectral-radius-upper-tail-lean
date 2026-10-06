import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Noncommutative power perturbation bound, used for Lie products.
No commutation between the two elements is assumed. -/
theorem algebra_power_difference_le (x y : A) {M : ℝ}
    (hM : 0 ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (n : ℕ) :
    ‖x^(n+1)-y^(n+1)‖ ≤ ((n+1 : ℕ) : ℝ)*M^n*‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x^(n+1+1)-y^(n+1+1) =
        (x^(n+1)-y^(n+1))*x+y^(n+1)*(x-y) := by
      simp only [pow_succ, sub_mul, mul_sub]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖(x^(n+1)-y^(n+1))*x‖+‖y^(n+1)*(x-y)‖ := norm_add_le _ _
      _ ≤ ‖x^(n+1)-y^(n+1)‖*‖x‖+‖y^(n+1)‖*‖x-y‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (((n+1 : ℕ) : ℝ)*M^n*‖x-y‖)*M+M^(n+1)*‖x-y‖ := by
        apply add_le_add
        · exact mul_le_mul ih hx (norm_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_right
            ((norm_pow_le y (n+1)).trans (pow_le_pow_left₀ (norm_nonneg y) hy _))
            (norm_nonneg _)
      _ = _ := by push_cast; ring

#print axioms algebra_power_difference_le
end SpectralRadiusUpperTail
