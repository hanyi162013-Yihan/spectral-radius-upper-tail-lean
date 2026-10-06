import SpectralRadiusUpperTail.IidAverageEnergy
import SpectralRadiusUpperTail.IidRegularizedLogDetIntegrable

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius

lemma matrix_frobenius_sq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A‖^2 = ∑ i, ∑ j, ‖A i j‖^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rw [Real.sq_sqrt (by positivity)]

lemma normalized_frobenius_energy {n : ℕ} (x : Fin n × Fin n → ℂ) :
    ‖normalizedIidMatrix x‖^2/(n : ℝ) = averageEntryEnergy x := by
  unfold normalizedIidMatrix
  rw [norm_smul, mul_pow, RCLike.norm_ofReal, sq_abs, div_pow, one_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), matrix_frobenius_sq_sum]
  simp only [Matrix.of_apply]
  unfold averageEntryEnergy
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  ring

lemma frobenius_scalar_one_sq (n : ℕ) (b : ℝ) :
    ‖(b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)‖^2 = (n : ℝ)*b^2 := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    matrix_frobenius_sq_sum]
  simp [Matrix.one_apply, apply_ite, mul_comm]

lemma normalized_regularizedLogDet_energy_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n × Fin n → ℂ) (b s : ℝ) (hs : 0 < s) :
    matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ) ≤
      2*averageEntryEnergy x+2*b^2+s := by
  let A := normalizedIidMatrix x
  let B := (b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hh : ‖A-B‖^2 ≤ 2*‖A‖^2+2*‖B‖^2 := by
    have ht := norm_sub_le A B
    have hs := sq_nonneg (‖A‖-‖B‖)
    nlinarith [norm_nonneg (A-B), norm_nonneg A, norm_nonneg B]
  have hu := (matrixRegularizedLogDet_upper_energy A b s hs).trans
    (add_le_add hh (le_refl ((n : ℝ)*s)))
  have hd := div_le_div_of_nonneg_right hu (Nat.cast_nonneg n)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hB : ‖B‖^2 = (n : ℝ)*b^2 := frobenius_scalar_one_sq n b
  rw [hB] at hd
  calc
    _ ≤ (2*‖normalizedIidMatrix x‖^2+2*((n : ℝ)*b^2)+(n : ℝ)*s)/(n : ℝ) := hd
    _ = 2*(‖normalizedIidMatrix x‖^2/(n : ℝ))+2*b^2+s := by field_simp
    _ = _ := by rw [normalized_frobenius_energy]

#print axioms matrix_frobenius_sq_sum
#print axioms normalized_frobenius_energy
#print axioms frobenius_scalar_one_sq
#print axioms normalized_regularizedLogDet_energy_bound
end SpectralRadiusUpperTail
