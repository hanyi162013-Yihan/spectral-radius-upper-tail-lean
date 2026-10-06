import SpectralRadiusUpperTail.LogFactorialRate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

noncomputable def witnessPrefactor (n : ℕ) (u : ℝ) : ℝ :=
  ((n-1).factorial : ℝ)*u^n/(n : ℝ)^(n-1)

lemma witnessPrefactor_log_identity (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u) :
    Real.log (witnessPrefactor n u)/(n : ℝ) =
      Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ)+Real.log u := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hmp : (0 : ℝ) < (m+1 : ℕ) := by positivity
  simp only [witnessPrefactor,Nat.succ_sub_one,Nat.factorial_succ,Nat.cast_mul]
  rw [Real.log_div (mul_pos hm (pow_pos hu _)).ne' (pow_pos hmp _).ne',
    Real.log_mul hm.ne' (pow_pos hu _).ne',Real.log_pow,Real.log_pow,
    Real.log_mul hmp.ne' hm.ne']
  push_cast
  field_simp
  <;> ring

lemma witnessPrefactor_log_rate (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ => Real.log (witnessPrefactor n u)/(n : ℝ))
      atTop (𝓝 (Real.log u-1)) := by
  have he : (fun n : ℕ => Real.log (witnessPrefactor n u)/(n : ℝ)) =ᶠ[atTop]
      (fun n => Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ)+Real.log u) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact witnessPrefactor_log_identity n (by omega) u hu
  apply Filter.Tendsto.congr' he.symm
  simpa only [sub_eq_add_neg,add_comm] using log_factorial_rate_limit.add_const (Real.log u)

#print axioms witnessPrefactor
#print axioms witnessPrefactor_log_identity
#print axioms witnessPrefactor_log_rate
end SpectralRadiusUpperTail
