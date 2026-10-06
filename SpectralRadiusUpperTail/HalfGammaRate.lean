import SpectralRadiusUpperTail.HalfGammaUpper
import SpectralRadiusUpperTail.LogFactorialRate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma half_gamma_rate_le_factorial (n : ℕ) (hn : 4 ≤ n) :
    Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-Real.log ((n : ℝ)/2)/2 ≤
      (Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))/2+
        (Real.log (Real.sqrt Real.pi)/(n : ℝ)+Real.log (n : ℝ)/(n : ℝ))/2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hg := half_gamma_log_upper n hn
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ)/2+1/2)
    (show (n : ℝ)/2+1/2 ≤ n by linarith)
  rw [Real.log_div hnpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have ha : Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-(Real.log (n : ℝ)-Real.log 2)/2 =
      (2*Real.log (Real.Gamma ((n : ℝ)/2+1))-(n : ℝ)*Real.log (n : ℝ)+(n : ℝ)*Real.log 2)/(2*(n : ℝ)) := by
    field_simp
    <;> ring
  have hb : (Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))/2+
        (Real.log (Real.sqrt Real.pi)/(n : ℝ)+Real.log (n : ℝ)/(n : ℝ))/2 =
      (Real.log (n.factorial : ℝ)-(n : ℝ)*Real.log (n : ℝ)+Real.log (Real.sqrt Real.pi)+Real.log (n : ℝ))/(2*(n : ℝ)) := by
    field_simp
    <;> ring
  rw [ha,hb]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

lemma half_gamma_rate_eventual_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-Real.log ((n : ℝ)/2)/2 ≤ -1/2+ε := by
  have hc : Tendsto (fun n : ℕ => Real.log (Real.sqrt Real.pi)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ht := (log_factorial_rate_limit.div_const 2).add ((hc.add hl).div_const 2)
  have ht' : Tendsto (fun n : ℕ =>
      (Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))/2+
        (Real.log (Real.sqrt Real.pi)/(n : ℝ)+Real.log (n : ℝ)/(n : ℝ))/2)
      atTop (𝓝 (-1/2)) := by simpa using ht
  filter_upwards [(tendsto_order.1 ht').2 (-1/2+ε) (by linarith),eventually_ge_atTop (4 : ℕ)] with n hn hn4
  exact (half_gamma_rate_le_factorial n hn4).trans hn.le

#print axioms half_gamma_rate_le_factorial
#print axioms half_gamma_rate_eventual_upper
end SpectralRadiusUpperTail
