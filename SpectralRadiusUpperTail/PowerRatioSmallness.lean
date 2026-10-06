import Mathlib.Analysis.SpecificLimits.Normed

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma power_div_dimension_le_inverse (q n K : ℝ) (hq : 1 ≤ q) (hn : 0 < n)
    (p d : ℕ) (hpd : p < d) (h : q^d ≤ K*n) : q^p/n ≤ K/q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hp : q^(p+1) ≤ q^d := pow_le_pow_right₀ hq (by omega)
  rw [div_le_div_iff₀ hn hq0]
  simpa only [pow_succ] using hp.trans h

lemma power_div_dimension_tendsto {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (p d : ℕ) (hpd : p < d) (K : ℝ)
    (h : ∀ᶠ n in atTop, (q n : ℝ)^d ≤ K*(n : ℝ)) :
    Tendsto (fun n => (q n : ℝ)^p/(n : ℝ)) atTop (𝓝 0) := by
  have hqr : Tendsto (fun n => (q n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hq
  have ht : Tendsto (fun n => K/(q n : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hqr
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ ht
  filter_upwards [h,hq.eventually_ge_atTop 1,eventually_ge_atTop (1 : ℕ)] with n hn hqn hn1
  exact power_div_dimension_le_inverse _ _ K (by exact_mod_cast hqn)
    (by exact_mod_cast hn1) p d hpd hn

lemma dimension_mul_geometric_tendsto {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (d : ℕ) (h : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ (q n : ℝ)^d)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => (n : ℝ)*a^(q n)) atTop (𝓝 0) := by
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one d ha ha1).comp hq
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ ht
  filter_upwards [h] with n hn
  exact mul_le_mul_of_nonneg_right hn (pow_nonneg ha _)

#print axioms power_div_dimension_le_inverse
#print axioms power_div_dimension_tendsto
#print axioms dimension_mul_geometric_tendsto
end SpectralRadiusUpperTail
