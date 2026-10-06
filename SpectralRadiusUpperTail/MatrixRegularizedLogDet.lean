import SpectralRadiusUpperTail.HermitianShiftDeterminant
import SpectralRadiusUpperTail.ExteriorLogDetDerivative

namespace SpectralRadiusUpperTail
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable def matrixRegularizedLogDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b s : ℝ) : ℝ :=
  Real.log ‖(((A-(b : ℂ) • 1).conjTranspose*(A-(b : ℂ) • 1))+(s : ℂ) • 1).det‖

lemma matrixRegularizedLogDet_floor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b s : ℝ) (hs : 0 < s) : (n : ℝ)*Real.log s ≤ matrixRegularizedLogDet A b s := by
  have hH := Matrix.posSemidef_conjTranspose_mul_self (A-(b : ℂ) • 1)
  have hh := (posSemidef_shift_det_lower _ hH s hs.le).1
  have hl := Real.log_le_log (pow_pos hs n) hh
  convert! hl using 1
  simp only [Real.log_pow]

lemma matrix_gram_det_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖(A.conjTranspose*A).det‖ = ‖A.det‖^2 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, pow_two]

lemma matrix_shift_det_norm_sub_comm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b : ℝ) :
    ‖(A-(b : ℂ) • 1).det‖ = ‖((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det‖ := by
  have he : A-(b : ℂ) • 1 = -((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-A) := by abel
  rw [he, Matrix.det_neg, norm_mul, norm_pow]
  simp

lemma matrixRegularizedLogDet_ge_unregularized {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (b s : ℝ) (hs : 0 ≤ s)
    (hb : (b : ℂ) ∈ resolventSet ℂ A) :
    2*Real.log ‖((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det‖ ≤
      matrixRegularizedLogDet A b s := by
  have hH := Matrix.posSemidef_conjTranspose_mul_self (A-(b : ℂ) • 1)
  have hh := (posSemidef_shift_det_lower _ hH s hs).2
  have hpos : 0 < ‖((A-(b : ℂ) • 1).conjTranspose*(A-(b : ℂ) • 1)).det‖ := by
    rw [matrix_gram_det_norm, matrix_shift_det_norm_sub_comm]
    exact sq_pos_of_pos (norm_pos_iff.mpr (shiftedDeterminant_ne_zero A b hb))
  have hl := Real.log_le_log hpos hh
  rw [matrix_gram_det_norm, matrix_shift_det_norm_sub_comm, Real.log_pow] at hl
  convert! hl using 1

lemma normalized_matrixRegularizedLogDet_floor {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (b s : ℝ) (hs : 0 < s) :
    Real.log s ≤ matrixRegularizedLogDet A b s/(n : ℝ) := by
  exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr
    (by simpa only [mul_comm] using matrixRegularizedLogDet_floor A b s hs)

lemma normalized_matrixRegularizedLogDet_ge_exterior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (b s : ℝ) (hs : 0 ≤ s)
    (hb : (b : ℂ) ∈ resolventSet ℂ A) :
    2*normalizedExteriorLogDet A b ≤ matrixRegularizedLogDet A b s/(n : ℝ) := by
  have hh := div_le_div_of_nonneg_right (matrixRegularizedLogDet_ge_unregularized A b s hs hb)
    (Nat.cast_nonneg n)
  simpa only [normalizedExteriorLogDet, mul_div_assoc] using hh

#print axioms matrixRegularizedLogDet
#print axioms matrixRegularizedLogDet_floor
#print axioms matrix_gram_det_norm
#print axioms matrix_shift_det_norm_sub_comm
#print axioms matrixRegularizedLogDet_ge_unregularized
#print axioms normalized_matrixRegularizedLogDet_floor
#print axioms normalized_matrixRegularizedLogDet_ge_exterior
end SpectralRadiusUpperTail
