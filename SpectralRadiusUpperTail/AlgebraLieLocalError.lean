import SpectralRadiusUpperTail.AlgebraExponentialRemainder

namespace SpectralRadiusUpperTail
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

lemma algebra_exp_sub_one_le (a : A) (ha : ‖a‖ ≤ 1) :
    ‖NormedSpace.exp a-1‖ ≤ 2*‖a‖ := by
  have h := algebra_exp_remainder_le a ha
  calc
    _ = ‖(NormedSpace.exp a-1-a)+a‖ := by congr 1; abel
    _ ≤ ‖NormedSpace.exp a-1-a‖+‖a‖ := norm_add_le _ _
    _ ≤ ‖a‖^2+‖a‖ := add_le_add h le_rfl
    _ ≤ _ := by nlinarith [norm_nonneg a]

/-- Uniform quadratic local error for the noncommutative Lie product. -/
theorem algebra_lie_local_error (a b : A) (h : ‖a‖+‖b‖ ≤ 1) :
    ‖NormedSpace.exp a*NormedSpace.exp b-NormedSpace.exp (a+b)‖ ≤
      (Real.exp 1+4)*(‖a‖+‖b‖)^2 := by
  have ha : ‖a‖ ≤ 1 := by linarith [norm_nonneg b]
  have hb : ‖b‖ ≤ 1 := by linarith [norm_nonneg a]
  have hab : ‖a+b‖ ≤ 1 := (norm_add_le _ _).trans h
  have he : NormedSpace.exp a*NormedSpace.exp b-NormedSpace.exp (a+b) =
      (NormedSpace.exp a-1-a)*NormedSpace.exp b+
      a*(NormedSpace.exp b-1)+(NormedSpace.exp b-1-b)-
      (NormedSpace.exp (a+b)-1-(a+b)) := by noncomm_ring
  have h1 := norm_mul_le (NormedSpace.exp a-1-a) (NormedSpace.exp b)
  have h2 := norm_mul_le a (NormedSpace.exp b-1)
  have heB : ‖NormedSpace.exp b‖ ≤ Real.exp 1 :=
    (algebra_exp_norm_le b).trans (Real.exp_le_exp.mpr hb)
  have hA := algebra_exp_remainder_le a ha
  have hB := algebra_exp_remainder_le b hb
  have hAB := algebra_exp_remainder_le (a+b) hab
  have hnorm : ‖a+b‖^2 ≤ (‖a‖+‖b‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
  rw [he]
  calc
    _ ≤ ‖(NormedSpace.exp a-1-a)*NormedSpace.exp b+
        a*(NormedSpace.exp b-1)+(NormedSpace.exp b-1-b)‖+
        ‖NormedSpace.exp (a+b)-1-(a+b)‖ := norm_sub_le _ _
    _ ≤ (‖(NormedSpace.exp a-1-a)*NormedSpace.exp b‖+
        ‖a*(NormedSpace.exp b-1)‖)+‖NormedSpace.exp b-1-b‖+
        ‖NormedSpace.exp (a+b)-1-(a+b)‖ := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖a‖^2*Real.exp 1+‖a‖*(2*‖b‖)+‖b‖^2+(‖a‖+‖b‖)^2 := by
      exact add_le_add (add_le_add
        (add_le_add (h1.trans (mul_le_mul hA heB (norm_nonneg _) (sq_nonneg _)))
          (h2.trans (mul_le_mul_of_nonneg_left (algebra_exp_sub_one_le b hb) (norm_nonneg _))))
        hB) (hAB.trans hnorm)
    _ ≤ _ := by
      have hp : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have hsq : ‖a‖^2 ≤ (‖a‖+‖b‖)^2 := by nlinarith [norm_nonneg a, norm_nonneg b]
      have hm := mul_le_mul_of_nonneg_right hsq hp
      nlinarith [norm_nonneg a, norm_nonneg b, mul_nonneg (norm_nonneg a) (norm_nonneg b)]

#print axioms algebra_lie_local_error
end SpectralRadiusUpperTail
