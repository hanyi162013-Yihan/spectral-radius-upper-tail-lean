import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma eventual_log_lower_of_power_lower (p : ℕ → ℝ) (q : ℝ) (hq : 0 < q)
    (h : ∀ᶠ n : ℕ in atTop, q^n/2 ≤ p n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log q-ε ≤ Real.log (p n)/(n : ℝ) := by
  have ht : Tendsto (fun n : ℕ => Real.log 2/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hs := (tendsto_order.1 ht).2 ε hε
  filter_upwards [h,hs,eventually_ge_atTop (1 : ℕ)] with n hn hs hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < q^n/2) hn
  rw [Real.log_div (pow_ne_zero _ hq.ne') (by norm_num : (2 : ℝ) ≠ 0),Real.log_pow] at hh
  apply (le_div_iff₀ hnpos).mpr
  have hsmall := (div_lt_iff₀ hnpos).mp hs
  nlinarith

#print axioms eventual_log_lower_of_power_lower
end SpectralRadiusUpperTail
