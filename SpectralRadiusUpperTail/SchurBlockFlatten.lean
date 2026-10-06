import SpectralRadiusUpperTail.RealSchurPaddedMatrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius BigOperators

lemma real_frobenius_norm_sq_finite {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _))

/-- Regard an `N × N` array of `2 × 2` blocks as one real matrix. -/
noncomputable def flattenSchurBlocks {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ)) :
    Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℝ :=
  Matrix.of (fun a b => A a.1 b.1 a.2 b.2)

theorem flattenSchurBlocks_mul {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ)) :
    flattenSchurBlocks (A*B) =
      flattenSchurBlocks A * flattenSchurBlocks B := by
  ext a b
  simp only [flattenSchurBlocks, Matrix.of_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.mul_apply]

theorem flattenSchurBlocks_one {N : ℕ} :
    flattenSchurBlocks (1 : Matrix (Fin N) (Fin N)
      (Matrix (Fin 2) (Fin 2) ℝ)) = 1 := by
  ext a b
  simp only [flattenSchurBlocks, Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;>
    simp [h1, h2, Prod.ext_iff, Matrix.one_apply]

theorem flattenSchurBlocks_pow {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (k : ℕ) :
    flattenSchurBlocks (A^k) = (flattenSchurBlocks A)^k := by
  induction k with
  | zero => simpa only [pow_zero] using (flattenSchurBlocks_one (N := N))
  | succ k ih => rw [pow_succ, flattenSchurBlocks_mul, ih, pow_succ]

theorem flattenSchurBlocks_norm_sq {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ)) :
    ‖flattenSchurBlocks A‖^2 =
      ∑ i : Fin N, ∑ j : Fin N, ‖A i j‖^2 := by
  rw [real_frobenius_norm_sq_finite]
  simp only [flattenSchurBlocks, Matrix.of_apply, Fintype.sum_prod_type]
  simp_rw [real_frobenius_norm_sq_finite]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

#print axioms flattenSchurBlocks_norm_sq
#print axioms flattenSchurBlocks_mul
#print axioms flattenSchurBlocks_pow
end SpectralRadiusUpperTail
