import SpectralRadiusUpperTail.ScalarCoefficientTailBound

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

lemma resolvent_coefficient_error_le (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (k : ℕ) (r P C : ℝ)
    (hr : 1 ≤ r) (hz : r ≤ ‖z‖) (hu : z ∈ resolventSet ℂ A)
    (hP : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A^(k+1))‖ ≤ P)
    (hC : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (resolvent A z)‖ ≤ C) :
    ‖matrixCoefficient p q (resolvent A z) - z⁻¹*matrixCoefficient p q 1‖ ≤
      (∑ j ∈ Finset.range k, ‖matrixCoefficient p q (A^(j+1))‖) + P*C/r^(k+1) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr0.trans_le hz)
  have hzi : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (hr.trans hz)
  have he : matrixCoefficient p q (resolvent A z) - z⁻¹*matrixCoefficient p q 1 =
      (∑ j ∈ Finset.range k, (z⁻¹)^(j+1+1)*matrixCoefficient p q (A^(j+1))) +
        (z⁻¹)^(k+1)*matrixCoefficient p q (A^(k+1)*resolvent A z) := by
    rw [matrixCoefficient_resolvent_expansion p q A z hz0 hu (k+1),Finset.sum_range_succ']
    simp only [zero_add,pow_one,pow_zero]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (matrixCoefficient_remainder_bound p q hp hq A z (k+1) r P C hr0 hz hP hC)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,norm_pow]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (pow_le_one₀ (norm_nonneg _) hzi) (norm_nonneg (matrixCoefficient p q (A^(j+1))))

#print axioms resolvent_coefficient_error_le
end SpectralRadiusUpperTail
