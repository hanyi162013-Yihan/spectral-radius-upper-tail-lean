import SpectralRadiusUpperTail.AlgebraExponentialIntegrable

namespace SpectralRadiusUpperTail
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

lemma algebra_exp_add_commute {a b : A} (h : Commute a b) :
    NormedSpace.exp (a+b) = NormedSpace.exp a*NormedSpace.exp b := by
  apply NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
  · rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _
  · rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _

lemma algebra_exp_nat_smul (n : ℕ) (a : A) :
    NormedSpace.exp ((n : ℝ) • a) = NormedSpace.exp a^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul,
      algebra_exp_add_commute ((Commute.refl a).smul_left (n : ℝ)), ih, pow_succ]

lemma algebra_exp_div_pow (a : A) (n : ℕ) (hn : n ≠ 0) :
    (NormedSpace.exp ((n : ℝ)⁻¹ • a))^n = NormedSpace.exp a := by
  rw [← algebra_exp_nat_smul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

#print axioms algebra_exp_div_pow
end SpectralRadiusUpperTail
