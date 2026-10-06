import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma nonnegative_power_first_order (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 ≤ ε) (k : ℕ) :
    r^(k+1)+((k+1 : ℕ) : ℝ)*r^k*ε ≤ (r+ε)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := mul_le_mul_of_nonneg_right ih (add_nonneg hr hε)
    have hpos : 0 ≤ ((k+1 : ℕ) : ℝ)*r^k*ε^2 := by positivity
    simp only [pow_succ] at hh ⊢
    push_cast at hh hpos ⊢
    nlinarith

/-- An arbitrarily small spectral buffer absorbs the polynomial factor d
from a two-dimensional nonnormal block. -/
lemma power_derivative_buffer (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε) (k : ℕ) :
    ((k+1 : ℕ) : ℝ)*r^k ≤ (r+ε)^(k+1)/ε := by
  apply (le_div_iff₀ hε).mpr
  have hh := nonnegative_power_first_order r ε hr hε.le k
  have hp : 0 ≤ r^(k+1) := pow_nonneg hr _
  linarith

lemma schur_squared_power_buffer (r ε Δ : ℝ) (hr : 0 ≤ r) (hε : 0 < ε) (k : ℕ) :
    2*r^(2*(k+1)) + Δ^2*(((k+1 : ℕ) : ℝ)*r^k)^2 ≤
      (2+Δ^2/ε^2)*(r+ε)^(2*(k+1)) := by
  have h1 := pow_le_pow_left₀ hr (show r ≤ r+ε by linarith) (2*(k+1))
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ ((k+1 : ℕ) : ℝ)*r^k)
    (power_derivative_buffer r ε hr hε k) 2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg Δ)
  have he : ((r+ε)^(k+1)/ε)^2 = (r+ε)^(2*(k+1))/ε^2 := by
    rw [div_pow, ← pow_mul, Nat.mul_comm (k+1) 2]
  rw [he] at h3
  calc
    _ ≤ 2*(r+ε)^(2*(k+1)) + Δ^2*((r+ε)^(2*(k+1))/ε^2) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h3
    _ = _ := by ring

#print axioms nonnegative_power_first_order
#print axioms power_derivative_buffer
#print axioms schur_squared_power_buffer
end SpectralRadiusUpperTail
