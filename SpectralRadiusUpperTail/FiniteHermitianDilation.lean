import SpectralRadiusUpperTail.HermitianDilation
import SpectralRadiusUpperTail.NormalizedFrobeniusEnergy
import Mathlib.Logic.Equiv.Fin.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable def finiteHermitianDilation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n+n)) (Fin (n+n)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (hermitianDilation A)

lemma finiteHermitianDilation_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (finiteHermitianDilation A).IsHermitian :=
  (hermitianDilation_isHermitian A).reindex finSumFinEquiv

lemma matrix_frobenius_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ‖Matrix.reindex e e A‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  congr 1
  calc
    _ = ∑ i : κ, ∑ j : ι, ‖A (e.symm i) j‖^(2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.symm.sum_comp (fun j => ‖A (e.symm i) j‖^(2 : ℝ))
    _ = _ := e.symm.sum_comp (fun i => ∑ j, ‖A i j‖^(2 : ℝ))

lemma hermitianDilation_frobenius_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖hermitianDilation A‖^2 = 2*‖A‖^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rw [Real.sq_sqrt (by positivity), matrix_frobenius_sq_sum]
  simp only [Fintype.sum_sum_type, hermitianDilation, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, norm_zero, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
    zero_add, add_zero, Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]
  ring

lemma finiteHermitianDilation_frobenius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖finiteHermitianDilation A‖ = Real.sqrt 2*‖A‖ := by
  rw [finiteHermitianDilation, matrix_frobenius_reindex]
  have hs := hermitianDilation_frobenius_sq A
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hs

lemma finiteHermitianDilation_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    finiteHermitianDilation (A-B) = finiteHermitianDilation A-finiteHermitianDilation B := by
  have he : hermitianDilation (A-B) = hermitianDilation A-hermitianDilation B := by
    ext i j
    cases i <;> cases j <;> simp [hermitianDilation, Matrix.conjTranspose_sub]
  simp [finiteHermitianDilation, he, Matrix.reindex_apply, Matrix.submatrix_sub]

lemma finiteHermitianDilation_combination {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ) :
    finiteHermitianDilation ((a : ℂ) • A+(b : ℂ) • B) =
      (a : ℂ) • finiteHermitianDilation A+(b : ℂ) • finiteHermitianDilation B := by
  have he : hermitianDilation ((a : ℂ) • A+(b : ℂ) • B) =
      (a : ℂ) • hermitianDilation A+(b : ℂ) • hermitianDilation B := by
    ext i j
    cases i <;> cases j <;>
      simp [hermitianDilation, Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  unfold finiteHermitianDilation
  rw [he]
  rfl

#print axioms finiteHermitianDilation_isHermitian
#print axioms matrix_frobenius_reindex
#print axioms hermitianDilation_frobenius_sq
#print axioms finiteHermitianDilation_frobenius
#print axioms finiteHermitianDilation_sub
#print axioms finiteHermitianDilation_combination
end SpectralRadiusUpperTail
