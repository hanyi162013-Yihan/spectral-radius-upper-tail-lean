import SpectralRadiusUpperTail.NormalizedMatrixTrace
import SpectralRadiusUpperTail.ResolventFiniteExpansion

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

lemma normalizedMatrixTrace_sum {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    normalizedMatrixTrace (∑ i ∈ s, A i) = ∑ i ∈ s, normalizedMatrixTrace (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normalizedMatrixTrace]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, normalizedMatrixTrace_add, ih]

lemma normalizedTrace_resolvent_expansion (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : z ≠ 0) (hu : z ∈ resolventSet ℂ A) (k : ℕ) :
    normalizedMatrixTrace (resolvent A z) =
      (∑ j ∈ Finset.range k, (z⁻¹)^(j+1) * normalizedMatrixTrace (A^j)) +
        (z⁻¹)^k * normalizedMatrixTrace (A^k*resolvent A z) := by
  conv_lhs => rw [resolvent_finite_expansion A z hz hu k]
  rw [normalizedMatrixTrace_add, normalizedMatrixTrace_sum, normalizedMatrixTrace_smul]
  simp only [normalizedMatrixTrace_smul]

lemma normalizedTrace_resolvent_remainder (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (k : ℕ) (r P C : ℝ) (hr : 0 < r) (hz : r ≤ ‖z‖)
    (hP : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A^k)‖ ≤ P)
    (hC : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (resolvent A z)‖ ≤ C) :
    ‖(z⁻¹)^k * normalizedMatrixTrace (A^k*resolvent A z)‖ ≤ P*C/r^k := by
  have hP0 : 0 ≤ P := (norm_nonneg _).trans hP
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have hb := (normalizedMatrixTrace_norm_le (A^k*resolvent A z)).trans
    ((Matrix.l2_opNorm_mul (A^k) (resolvent A z)).trans
      (mul_le_mul hP hC (norm_nonneg _) hP0))
  rw [norm_mul, norm_pow, norm_inv, inv_pow]
  calc
    _ ≤ (‖z‖^k)⁻¹*(P*C) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = P*C/‖z‖^k := by ring
    _ ≤ P*C/r^k := div_le_div_of_nonneg_left (mul_nonneg hP0 hC0)
      (pow_pos hr _) (pow_le_pow_left₀ hr.le hz _)

lemma normalizedTrace_resolvent_error_le (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (k : ℕ) (r P C : ℝ)
    (hr : 1 ≤ r) (hz : r ≤ ‖z‖) (hu : z ∈ resolventSet ℂ A)
    (hP : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A^(k+1))‖ ≤ P)
    (hC : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (resolvent A z)‖ ≤ C) :
    ‖normalizedMatrixTrace (resolvent A z) - z⁻¹‖ ≤
      (∑ j ∈ Finset.range k, ‖normalizedMatrixTrace (A^(j+1))‖) + P*C/r^(k+1) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr0.trans_le hz)
  have hzi : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (hr.trans hz)
  have he : normalizedMatrixTrace (resolvent A z) - z⁻¹ =
      (∑ j ∈ Finset.range k, (z⁻¹)^(j+1+1)*normalizedMatrixTrace (A^(j+1))) +
        (z⁻¹)^(k+1)*normalizedMatrixTrace (A^(k+1)*resolvent A z) := by
    rw [normalizedTrace_resolvent_expansion A z hz0 hu (k+1), Finset.sum_range_succ']
    simp only [zero_add, pow_one, pow_zero, normalizedMatrixTrace_one hn, mul_one]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (normalizedTrace_resolvent_remainder A z (k+1) r P C hr0 hz hP hC)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_pow]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (pow_le_one₀ (norm_nonneg _) hzi) (norm_nonneg (normalizedMatrixTrace (A^(j+1))))

#print axioms normalizedMatrixTrace_sum
#print axioms normalizedTrace_resolvent_expansion
#print axioms normalizedTrace_resolvent_remainder
#print axioms normalizedTrace_resolvent_error_le
end SpectralRadiusUpperTail
