import SpectralRadiusUpperTail.RealGinibreFirstDensity
import SpectralRadiusUpperTail.RealGinibreCoreUnitRatio
import SpectralRadiusUpperTail.RealGinibreRateGapUniform
import SpectralRadiusUpperTail.RealGinibreFirstCorePrefactor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The faster finite-Poisson real one-point term is bounded uniformly on
`r ≥ 1` by a subexponential multiple of the uncut dominant factor. -/
theorem realGinibreFirstDensity_le_exp_core_of_budget
    (n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hbudget : Real.log (n : ℝ)-
        Real.log (realGinibreCoreDensity n 1)+1/2 ≤ (n : ℝ)*ε)
    (r : ℝ) (hr : 1 ≤ r) :
    realGinibreFirstDensity n r ≤
      Real.exp ((n : ℝ)*ε)*realGinibreCoreDensity n r := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hrpos : 0 < r := by linarith
  have hQpos := realGinibreCoreDensity_pos n (by omega) r hrpos
  have hqratio := realGinibreCoreDensity_log_unit_ratio n (by omega) r hrpos
  have hgap := realGinibre_log_sub_rate_uniform n hn r hr
  have hrate2 : rate 2 r = 2*rate 1 r := by unfold rate; ring
  have hlogineq : Real.log (n : ℝ)-(n : ℝ)*rate 2 r ≤
      (n : ℝ)*ε+Real.log (realGinibreCoreDensity n r) := by
    rw [hqratio, hrate2]
    linarith
  have hpi : 1 ≤ 2*Real.pi := by nlinarith [Real.pi_gt_three]
  have hden : 0 < 2*Real.pi := by positivity
  have hfrac : (n : ℝ)/(2*Real.pi) ≤ (n : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpi hnR.le]
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt ((n : ℝ)/(2*Real.pi)) ≤ (n : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hnR.le
    · exact hfrac.trans (by nlinarith [hnOne])
  calc
    realGinibreFirstDensity n r ≤
        Real.sqrt ((n : ℝ)/(2*Real.pi)) *
          Real.exp (-(n : ℝ)*rate 2 r) :=
      (realGinibreFirstDensity_bound n hn r hr).2
    _ ≤ (n : ℝ)*Real.exp (-(n : ℝ)*rate 2 r) :=
      mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le
    _ = Real.exp (Real.log (n : ℝ)-(n : ℝ)*rate 2 r) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hnR]
      rw [neg_mul]
    _ ≤ Real.exp ((n : ℝ)*ε+Real.log (realGinibreCoreDensity n r)) :=
      Real.exp_le_exp.mpr hlogineq
    _ = _ := by rw [Real.exp_add, Real.exp_log hQpos]

theorem realGinibreFirstDensity_le_exp_core_eventual
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℝ, 1 ≤ r →
      realGinibreFirstDensity n r ≤
        Real.exp ((n : ℝ)*ε)*realGinibreCoreDensity n r := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    realGinibre_first_core_prefactor_eventual ε hε]
    with n hn hbudget r hr
  exact realGinibreFirstDensity_le_exp_core_of_budget n hn ε hbudget r hr

/-- The same comparison without the square-root prefactor, used for the
nonreal one-point Poisson envelope. -/
theorem realGinibrePoissonEnvelope_le_exp_core_of_budget
    (n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hbudget : Real.log (n : ℝ)-
        Real.log (realGinibreCoreDensity n 1)+1/2 ≤ (n : ℝ)*ε)
    (r : ℝ) (hr : 1 ≤ r) :
    (n : ℝ)*Real.exp (-(n : ℝ)*rate 2 r) ≤
      Real.exp ((n : ℝ)*ε)*realGinibreCoreDensity n r := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hrpos : 0 < r := by linarith
  have hQpos := realGinibreCoreDensity_pos n (by omega) r hrpos
  have hqratio := realGinibreCoreDensity_log_unit_ratio n (by omega) r hrpos
  have hgap := realGinibre_log_sub_rate_uniform n hn r hr
  have hrate2 : rate 2 r = 2*rate 1 r := by unfold rate; ring
  have hlogineq : Real.log (n : ℝ)-(n : ℝ)*rate 2 r ≤
      (n : ℝ)*ε+Real.log (realGinibreCoreDensity n r) := by
    rw [hqratio, hrate2]
    linarith
  calc
    _ = Real.exp (Real.log (n : ℝ)-(n : ℝ)*rate 2 r) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hnR, neg_mul]
    _ ≤ Real.exp ((n : ℝ)*ε+Real.log (realGinibreCoreDensity n r)) :=
      Real.exp_le_exp.mpr hlogineq
    _ = _ := by rw [Real.exp_add, Real.exp_log hQpos]

#print axioms realGinibreFirstDensity_le_exp_core_of_budget
#print axioms realGinibreFirstDensity_le_exp_core_eventual
#print axioms realGinibrePoissonEnvelope_le_exp_core_of_budget
end SpectralRadiusUpperTail
