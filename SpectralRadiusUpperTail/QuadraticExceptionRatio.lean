import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma quadratic_exception_div_normalizer_tendsto
    (Z : ℕ → ℝ) (hpos : ∀ n, 0 < Z n) (A : ℝ)
    (hZ : Tendsto (fun n => Real.log (Z n)/(n : ℝ)) atTop (𝓝 A))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    Tendsto (fun n : ℕ => C*Real.exp (-c*(n : ℝ)^2)/Z n) atTop (𝓝 0) := by
  have he : Tendsto (fun n : ℕ => C*Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hpos n).le)) _ he
  have hl := (tendsto_order.1 hZ).1 (A-1) (by linarith)
  have hnlarge : ∀ᶠ n : ℕ in atTop, (2-A)/c ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((2-A)/c))
  filter_upwards [hl,hnlarge,eventually_ge_atTop (1 : ℕ)] with n hn hlarge hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : (n : ℝ)*(A-1) ≤ Real.log (Z n) := by
    have hh := (lt_div_iff₀ hnpos).mp hn
    nlinarith
  have hlow : Real.exp ((n : ℝ)*(A-1)) ≤ Z n := by
    rw [← Real.exp_log (hpos n)]
    exact Real.exp_le_exp.mpr hlog
  have hquad : -c*(n : ℝ)^2-(n : ℝ)*(A-1) ≤ -(n : ℝ) := by
    have hh := (div_le_iff₀ hc).mp hlarge
    have hh' := mul_le_mul_of_nonneg_left hh hnpos.le
    nlinarith
  calc
    C*Real.exp (-c*(n : ℝ)^2)/Z n ≤
        C*Real.exp (-c*(n : ℝ)^2)/Real.exp ((n : ℝ)*(A-1)) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hlow
    _ = C*Real.exp (-c*(n : ℝ)^2-(n : ℝ)*(A-1)) := by rw [Real.exp_sub]; ring
    _ ≤ C*Real.exp (-(n : ℝ)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) hC

#print axioms quadratic_exception_div_normalizer_tendsto
end SpectralRadiusUpperTail
