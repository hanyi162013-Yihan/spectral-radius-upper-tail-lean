import SpectralRadiusUpperTail.HalfGammaRate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The other side of the duplication-formula estimate: monotonicity of
Gamma makes its upper half-step no smaller than its lower half-step. -/
lemma half_gamma_square_lower (n : ℕ) (hn : 4 ≤ n) :
    (n.factorial : ℝ) * (2 : ℝ)^(-(n : ℝ)) * Real.sqrt Real.pi ≤
      (Real.Gamma ((n : ℝ)/2+1))^2 := by
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hm := Real.Gamma_strictMonoOn_Ici.monotoneOn
    (show (n : ℝ)/2+1/2 ∈ Set.Ici (2 : ℝ) by exact (show (2 : ℝ) ≤ (n : ℝ)/2+1/2 by linarith))
    (show (n : ℝ)/2+1 ∈ Set.Ici (2 : ℝ) by exact (show (2 : ℝ) ≤ (n : ℝ)/2+1 by linarith))
    (by linarith : (n : ℝ)/2+1/2 ≤ (n : ℝ)/2+1)
  have hp := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ)/2+1)
  have hmul := mul_le_mul_of_nonneg_right hm hp.le
  have hd := Real.Gamma_mul_Gamma_add_half ((n : ℝ)/2+1/2)
  have he1 : (n : ℝ)/2+1/2+1/2 = (n : ℝ)/2+1 := by ring
  have he2 : 2*((n : ℝ)/2+1/2) = (n : ℝ)+1 := by ring
  have he3 : 1-2*((n : ℝ)/2+1/2) = -(n : ℝ) := by ring
  rw [he1,he3,he2,Real.Gamma_nat_eq_factorial] at hd
  calc
    _ = Real.Gamma ((n : ℝ)/2+1/2)*Real.Gamma ((n : ℝ)/2+1) := hd.symm
    _ ≤ _ := by simpa only [pow_two] using hmul

lemma half_gamma_log_lower (n : ℕ) (hn : 4 ≤ n) :
    Real.log (n.factorial : ℝ)-(n : ℝ)*Real.log 2+
      Real.log (Real.sqrt Real.pi) ≤
      2*Real.log (Real.Gamma ((n : ℝ)/2+1)) := by
  have hG := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ)/2+1)
  have hh := Real.log_le_log (by positivity)
    (half_gamma_square_lower n hn)
  rw [Real.log_pow,Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hh
  nlinarith

lemma half_gamma_rate_ge_factorial (n : ℕ) (hn : 4 ≤ n) :
    (Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))/2+
      Real.log (Real.sqrt Real.pi)/(2*(n : ℝ)) ≤
      Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-Real.log ((n : ℝ)/2)/2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hg := half_gamma_log_lower n hn
  rw [Real.log_div hnpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have ha :
      (Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))/2+
        Real.log (Real.sqrt Real.pi)/(2*(n : ℝ)) =
        (Real.log (n.factorial : ℝ)-(n : ℝ)*Real.log (n : ℝ)+
          Real.log (Real.sqrt Real.pi))/(2*(n : ℝ)) := by
    field_simp
    <;> ring
  have hb :
      Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-
        (Real.log (n : ℝ)-Real.log 2)/2 =
        (2*Real.log (Real.Gamma ((n : ℝ)/2+1))-
          (n : ℝ)*Real.log (n : ℝ)+(n : ℝ)*Real.log 2)/(2*(n : ℝ)) := by
    field_simp
    <;> ring
  rw [ha,hb]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

lemma half_gamma_rate_eventual_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      -1/2-ε ≤ Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-
        Real.log ((n : ℝ)/2)/2 := by
  have hc0 : Tendsto (fun n : ℕ => Real.log (Real.sqrt Real.pi)/(n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => Real.log (Real.sqrt Real.pi)/(2*(n : ℝ)))
      atTop (𝓝 0) := by
    have he : (fun n : ℕ => Real.log (Real.sqrt Real.pi)/(2*(n : ℝ))) =
        (fun n : ℕ => (Real.log (Real.sqrt Real.pi)/(n : ℝ))/2) := by
      funext n
      ring
    rw [he]
    simpa using hc0.div_const 2
  have ht := (log_factorial_rate_limit.div_const 2).add hc
  have ht' : Tendsto (fun n : ℕ =>
      (Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))/2+
        Real.log (Real.sqrt Real.pi)/(2*(n : ℝ))) atTop (𝓝 (-1/2)) := by
    simpa using ht
  filter_upwards [(tendsto_order.1 ht').1 (-1/2-ε) (by linarith),
      eventually_ge_atTop (4 : ℕ)] with n hn hn4
  exact hn.le.trans (half_gamma_rate_ge_factorial n hn4)

/-- The Gamma normalization needed for the real one-point density has its
sharp speed-`n` logarithmic asymptotic. -/
theorem half_gamma_rate_limit :
    Tendsto (fun n : ℕ =>
      Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-
        Real.log ((n : ℝ)/2)/2) atTop (𝓝 (-1/2)) := by
  apply (tendsto_order).2
  constructor
  · intro a ha
    have hε : 0 < ((-1/2 : ℝ)-a)/2 := by linarith
    filter_upwards [half_gamma_rate_eventual_lower _ hε] with n hn
    exact lt_of_lt_of_le (by linarith) hn
  · intro b hb
    have hε : 0 < (b-(-1/2 : ℝ))/2 := by linarith
    filter_upwards [half_gamma_rate_eventual_upper _ hε] with n hn
    exact lt_of_le_of_lt hn (by linarith)

#print axioms half_gamma_square_lower
#print axioms half_gamma_log_lower
#print axioms half_gamma_rate_eventual_lower
#print axioms half_gamma_rate_limit
end SpectralRadiusUpperTail
