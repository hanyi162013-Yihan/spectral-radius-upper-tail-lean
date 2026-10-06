import SpectralRadiusUpperTail.LogFactorialRate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma eventually_positive_polynomial_le_exp (D : ℝ) (hD : 0 < D) (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, D*(n : ℝ)^M ≤ Real.exp ((n : ℝ)*ε) := by
  have hc : Tendsto (fun n : ℕ => Real.log D/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => Real.log D/(n : ℝ)+(M : ℝ)*(Real.log (n : ℝ)/(n : ℝ)))
      atTop (𝓝 0) := by simpa using hc.add (hl.const_mul (M : ℝ))
  filter_upwards [(tendsto_order.1 ht).2 ε hε, eventually_gt_atTop 0] with n hn hn0
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hb : Real.log D+(M : ℝ)*Real.log (n : ℝ) ≤ (n : ℝ)*ε := by
    have hh : (Real.log D+(M : ℝ)*Real.log (n : ℝ))/(n : ℝ) < ε := by
      simpa only [add_div, mul_div_assoc] using hn
    have hx := (div_lt_iff₀ hnr).mp hh
    linarith
  calc
    D*(n : ℝ)^M = Real.exp (Real.log D+(M : ℝ)*Real.log (n : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hD, Real.exp_nat_mul, Real.exp_log hnr]
    _ ≤ _ := Real.exp_le_exp.mpr hb

lemma eventually_polynomial_prefactor_le_exp (C : ℝ) (hC : 0 ≤ C) (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*((n : ℝ)+1)^M ≤ Real.exp ((n : ℝ)*ε) := by
  have hh := eventually_positive_polynomial_le_exp ((C+1)*2^M) (by positivity) M ε hε
  filter_upwards [hh, eventually_ge_atTop 1] with n hn hn1
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  apply le_trans ?_ hn
  calc
    C*((n : ℝ)+1)^M ≤ (C+1)*(2*(n : ℝ))^M := by gcongr <;> linarith
    _ = _ := by rw [mul_pow]; ring

#print axioms eventually_positive_polynomial_le_exp
#print axioms eventually_polynomial_prefactor_le_exp
end SpectralRadiusUpperTail
