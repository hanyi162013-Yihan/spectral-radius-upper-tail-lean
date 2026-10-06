import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma eventually_quadratic_exp_le_linear (C q a : ℝ) (hC : 0 ≤ C) (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, C*Real.exp (-q*(n : ℝ)^2) ≤ Real.exp ((n : ℝ)*a) := by
  have hlarge : ∀ᶠ n : ℕ in atTop,
      max (Real.log (C+1)) ((1-a)/q) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with n hn
  have hl := (le_max_left _ _).trans hn
  have hqN := (div_le_iff₀ hq).mp ((le_max_right _ _).trans hn)
  have hmul := mul_le_mul_of_nonneg_right hqN (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  calc
    _ ≤ (C+1)*Real.exp (-q*(n : ℝ)^2) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (Real.log (C+1)-q*(n : ℝ)^2) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
      congr 2
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

lemma eventually_exp_prefactor_absorb (C a ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*Real.exp ((n : ℝ)*a) ≤ Real.exp ((n : ℝ)*(a+ε)) := by
  have hlarge : ∀ᶠ n : ℕ in atTop, Real.log (C+1)/ε ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with n hn
  have hh := (div_le_iff₀ hε).mp hn
  calc
    _ ≤ (C+1)*Real.exp ((n : ℝ)*a) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (Real.log (C+1)+(n : ℝ)*a) := by rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

lemma eventually_three_exponential_terms (C D q a b ε : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hq : 0 < q) (hba : b ≤ a) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      C*Real.exp ((n : ℝ)*a)+D*Real.exp (-q*(n : ℝ)^2)+Real.exp ((n : ℝ)*b) ≤
        Real.exp ((n : ℝ)*(a+ε)) := by
  filter_upwards [eventually_quadratic_exp_le_linear D q a hD hq,
    eventually_exp_prefactor_absorb (C+2) a ε (by positivity) hε] with n hquad hpref
  have hlin := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hba (Nat.cast_nonneg n))
  nlinarith

#print axioms eventually_quadratic_exp_le_linear
#print axioms eventually_exp_prefactor_absorb
#print axioms eventually_three_exponential_terms
end SpectralRadiusUpperTail
