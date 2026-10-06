import SpectralRadiusUpperTail.AlgebraLieLocalError
import SpectralRadiusUpperTail.AlgebraPowerDifference
import SpectralRadiusUpperTail.AlgebraExponentialPowers

namespace SpectralRadiusUpperTail
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

/-- Quantitative Lie-product estimate before choosing the step size. -/
theorem algebra_lie_power_error (a b : A) (t : ℝ) (ht : 0 ≤ t)
    (hsmall : t*(‖a‖+‖b‖) ≤ 1) (n : ℕ) :
    ‖(NormedSpace.exp (t • a)*NormedSpace.exp (t • b))^(n+1)-
      NormedSpace.exp ((((n+1 : ℕ) : ℝ)*t) • (a+b))‖ ≤
      ((n+1 : ℕ) : ℝ)*Real.exp ((n : ℝ)*t*(‖a‖+‖b‖))*
        ((Real.exp 1+4)*(t*(‖a‖+‖b‖))^2) := by
  let K := ‖a‖+‖b‖
  let X := NormedSpace.exp (t • a)*NormedSpace.exp (t • b)
  let Y := NormedSpace.exp (t • (a+b))
  have hnorm (z : A) : ‖t • z‖ = t*‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht]
  have hX : ‖X‖ ≤ Real.exp (t*K) := by
    calc
      _ ≤ ‖NormedSpace.exp (t • a)‖*‖NormedSpace.exp (t • b)‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖t • a‖*Real.exp ‖t • b‖ :=
        mul_le_mul (algebra_exp_norm_le _) (algebra_exp_norm_le _)
          (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, hnorm, hnorm]; congr 1; dsimp [K]; ring
  have hY : ‖Y‖ ≤ Real.exp (t*K) := by
    apply (algebra_exp_norm_le _).trans
    apply Real.exp_le_exp.mpr
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) ht
  have hloc : ‖X-Y‖ ≤ (Real.exp 1+4)*(t*K)^2 := by
    have hs : ‖t • a‖+‖t • b‖ ≤ 1 := by
      rw [hnorm, hnorm, ← mul_add]; exact hsmall
    have hh := algebra_lie_local_error (t • a) (t • b) hs
    simpa only [hnorm, ← mul_add, ← smul_add] using hh
  have hp := algebra_power_difference_le X Y (Real.exp_pos (t*K)).le hX hY n
  have he : Y^(n+1) = NormedSpace.exp ((((n+1 : ℕ) : ℝ)*t) • (a+b)) := by
    rw [← algebra_exp_nat_smul, smul_smul]
  change ‖X^(n+1)-_‖ ≤ _
  rw [← he]
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)*(Real.exp (t*K))^n*‖X-Y‖ := hp
    _ ≤ ((n+1 : ℕ) : ℝ)*(Real.exp (t*K))^n*((Real.exp 1+4)*(t*K)^2) :=
      mul_le_mul_of_nonneg_left hloc (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [K, mul_assoc]

#print axioms algebra_lie_power_error
end SpectralRadiusUpperTail
