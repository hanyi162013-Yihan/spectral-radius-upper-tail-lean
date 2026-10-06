import SpectralRadiusUpperTail.ResolventLogDetGap
import SpectralRadiusUpperTail.PhaseRotationLogDet
import SpectralRadiusUpperTail.IidRegularizedLogDetIntegrable

namespace SpectralRadiusUpperTail

noncomputable def complexRegularizedLogDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (s : ℝ) : ℝ :=
  Real.log ‖((A-z • 1).conjTranspose*(A-z • 1)+(s : ℂ) • 1).det‖

lemma complexRegularizedLogDet_measurable (n : ℕ) (z : ℂ) (s : ℝ) :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => complexRegularizedLogDet A z s) := by
  unfold complexRegularizedLogDet
  have hh : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      ((A-z • 1).conjTranspose*(A-z • 1)+(s : ℂ) • 1).det) := by fun_prop
  exact Real.measurable_log.comp hh.norm.measurable

lemma complex_shift_det_norm_comm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    ‖(A-z • 1).det‖ = ‖(z • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det‖ := by
  rw [show A-z • 1 = -(z • (1 : Matrix (Fin n) (Fin n) ℂ)-A) by abel,
    Matrix.det_neg, norm_mul, norm_pow]
  simp

lemma complexRegularizedLogDet_le_exterior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (s M : ℝ) (hs : 0 ≤ s) (hM : 0 < M)
    (hz : z ∈ resolventSet ℂ A)
    (hR : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (resolvent A z)‖ ≤ M) :
    complexRegularizedLogDet A z s ≤
      2*Real.log ‖(z • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det‖+(n : ℝ)*s*M^2 := by
  have hh := gram_logDet_regularization_gap (A-z • 1)
    (-Matrix.toEuclideanCLM (𝕜 := ℂ) (resolvent A z))
    (matrix_resolvent_negative_left_inverse A z hz) M s hM
    (by simpa only [norm_neg] using hR) hs
  rw [matrix_gram_det_norm, complex_shift_det_norm_comm, Real.log_pow] at hh
  change complexRegularizedLogDet A z s-_ ≤ _ at hh
  convert! (sub_le_iff_le_add).mp hh using 1 <;> ring

lemma normalized_complexRegularizedLogDet_le_exterior {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (s M : ℝ) (hs : 0 ≤ s) (hM : 0 < M)
    (hz : z ∈ resolventSet ℂ A)
    (hR : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (resolvent A z)‖ ≤ M) :
    complexRegularizedLogDet A z s/(n : ℝ) ≤ 2*normalizedComplexLogDet A z+s*M^2 := by
  have hh := div_le_div_of_nonneg_right (complexRegularizedLogDet_le_exterior A z s M hs hM hz hR)
    (Nat.cast_nonneg n)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  convert! hh using 1
  unfold normalizedComplexLogDet
  field_simp

#print axioms complexRegularizedLogDet
#print axioms complexRegularizedLogDet_measurable
#print axioms complex_shift_det_norm_comm
#print axioms complexRegularizedLogDet_le_exterior
#print axioms normalized_complexRegularizedLogDet_le_exterior
end SpectralRadiusUpperTail
