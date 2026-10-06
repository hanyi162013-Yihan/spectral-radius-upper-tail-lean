import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- A logarithmic cutoff beats the specified polynomial prefactor, with the
strict exponent condition displayed explicitly. -/
theorem polynomial_logarithmic_cutoff_tendsto (m : ℕ) (c B : ℝ)
    (h : (m : ℝ) < c*B^2) :
    Tendsto (fun n : ℕ => (n : ℝ)^m*Real.exp (-c*(B*Real.sqrt (Real.log (n : ℝ)))^2))
      atTop (𝓝 0) := by
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hl.const_mul_atTop (sub_pos.mpr h))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have he : (n : ℝ)^m = Real.exp ((m : ℝ)*Real.log (n : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hn0]
  change Real.exp (-((c*B^2-(m : ℝ))*Real.log (n : ℝ))) = _
  rw [mul_pow, Real.sq_sqrt (Real.log_nonneg hn1), he, ← Real.exp_add]
  congr 1
  ring

/-- The cutoff scale divided by sqrt(n) vanishes. -/
theorem sqrt_log_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).sqrt
  simpa only [Function.comp_def, id_eq, Real.sqrt_zero,
    Real.sqrt_div' _ (Nat.cast_nonneg _)] using hh

/-- The full affine cutoff factor used by the conditional truncation bound. -/
theorem affine_sqrt_log_flat_tendsto (A L b : ℝ) :
    Tendsto (fun n : ℕ => (A*Real.sqrt (Real.log (n : ℝ))+b)*(L/Real.sqrt (n : ℝ)))
      atTop (𝓝 0) := by
  have hflat : Tendsto (fun n : ℕ => L/Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hh := (sqrt_log_div_sqrt_tendsto.const_mul (A*L)).add (hflat.const_mul b)
  convert! hh using 1
  · funext n
    ring
  · ring

#print axioms polynomial_logarithmic_cutoff_tendsto
#print axioms affine_sqrt_log_flat_tendsto
end SpectralRadiusUpperTail
