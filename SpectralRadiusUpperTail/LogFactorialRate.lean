import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma log_factorial_rate_identity (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ) =
      Real.log (Stirling.stirlingSeq n)/(n : ℝ)+
        (Real.log 2+Real.log (n : ℝ))/(2*(n : ℝ))-1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [Stirling.stirlingSeq,Real.log_div hfac.ne' (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) hnpos.ne',Real.log_pow,
    Real.log_div hnpos.ne' (Real.exp_ne_zero 1),Real.log_exp]
  field_simp
  <;> ring

lemma log_factorial_rate_limit :
    Tendsto (fun n : ℕ => Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))
      atTop (𝓝 (-1)) := by
  have hs := (Real.continuousAt_log (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))).tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi
  have ht : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)/(n : ℝ)) atTop (𝓝 0) :=
    hs.div_atTop tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => Real.log 2/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (ht.add ((hc.add hl).div_const 2)).sub_const 1
  have he : (fun n : ℕ => Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ)) =ᶠ[atTop]
      (fun n => Real.log (Stirling.stirlingSeq n)/(n : ℝ)+
        ((Real.log 2/(n : ℝ)+Real.log (n : ℝ)/(n : ℝ))/2)-1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [log_factorial_rate_identity n (by omega)]
    ring
  apply Filter.Tendsto.congr' he.symm
  simpa using hh

#print axioms log_factorial_rate_identity
#print axioms log_factorial_rate_limit
end SpectralRadiusUpperTail
