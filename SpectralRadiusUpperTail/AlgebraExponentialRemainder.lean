import SpectralRadiusUpperTail.AlgebraExponentialIntegrable

namespace SpectralRadiusUpperTail
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

lemma algebra_exp_remainder_series (a : A) :
    NormedSpace.exp a-1-a =
      ∑' n : ℕ, (((n+2).factorial : ℝ)⁻¹) • a^(n+2) := by
  have h := (NormedSpace.expSeries_summable' (𝕂 := ℝ) a).sum_add_tsum_nat_add 2
  have he : (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • a^n) = NormedSpace.exp a := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  rw [he] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul,
    zero_add] at h
  rw [← h]
  abel

/-- Quadratic Taylor remainder in a real Banach algebra. -/
theorem algebra_exp_remainder_le (a : A) (ha : ‖a‖ ≤ 1) :
    ‖NormedSpace.exp a-1-a‖ ≤ ‖a‖^2 := by
  have hs := (summable_nat_add_iff 2).mpr
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) a)
  have hr := (summable_nat_add_iff 2).mpr
    (NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖a‖)
  have hb : ‖NormedSpace.exp a-1-a‖ ≤ Real.exp ‖a‖-1-‖a‖ := by
    rw [algebra_exp_remainder_series]
    calc
      _ ≤ ∑' n : ℕ, ‖(((n+2).factorial : ℝ)⁻¹) • a^(n+2)‖ :=
        norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ, (((n+2).factorial : ℝ)⁻¹) • ‖a‖^(n+2) := by
        apply Summable.tsum_le_tsum _ hs hr
        intro n
        rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (norm_pow_le a (n+2)) (by positivity)
      _ = _ := by rw [← algebra_exp_remainder_series, ← Real.exp_eq_exp_ℝ]
  exact hb.trans ((le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_norm, norm_norm] using
      Real.norm_exp_sub_one_sub_id_le (x := ‖a‖) (by simpa using ha)))

#print axioms algebra_exp_remainder_series
#print axioms algebra_exp_remainder_le
end SpectralRadiusUpperTail
