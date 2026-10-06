import SpectralRadiusUpperTail.GaussianMatrixSandwich

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.Frobenius

lemma gaussian_scaled_sandwich_norm_sq {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin c) (Fin d) ℝ)
    (t : ℝ) (x : Fin b × Fin c → ℝ) :
    ‖A*(t • gaussianEntryBlock x)*B‖^2 = t^2*‖A*gaussianEntryBlock x*B‖^2 := by
  rw [Matrix.mul_smul, Matrix.smul_mul, norm_smul, mul_pow]
  simp only [Real.norm_eq_abs, sq_abs]

theorem gaussian_scaled_sandwich_second_moment {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin c) (Fin d) ℝ) (t : ℝ) :
    Integrable (fun x : Fin b × Fin c → ℝ => ‖A*(t • gaussianEntryBlock x)*B‖^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : Fin b × Fin c → ℝ, ‖A*(t • gaussianEntryBlock x)*B‖^2
      ∂Measure.pi (fun _ => standardNormal)) = t^2*‖A‖^2*‖B‖^2 := by
  have hh := gaussian_matrix_sandwich_second_moment A B
  simp_rw [gaussian_scaled_sandwich_norm_sq]
  refine ⟨hh.1.const_mul _, ?_⟩
  rw [integral_const_mul, hh.2]
  ring

lemma matrix_sandwich_norm_sq_bound {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (N : Matrix (Fin b) (Fin c) ℝ)
    (B : Matrix (Fin c) (Fin d) ℝ) (t : ℝ) :
    ‖A*(t • N)*B‖^2 ≤ (t^2*‖B‖^2)*(‖A‖^2*‖N‖^2) := by
  have h := (Matrix.frobenius_norm_mul (A*(t • N)) B).trans
    (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul A (t • N)) (norm_nonneg B))
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_smul] at hs
  simpa only [mul_pow, Real.norm_eq_abs, sq_abs, mul_assoc, mul_left_comm, mul_comm] using hs

#print axioms matrix_sandwich_norm_sq_bound
#print axioms gaussian_scaled_sandwich_second_moment
end SpectralRadiusUpperTail
