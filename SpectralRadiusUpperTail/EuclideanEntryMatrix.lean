import SpectralRadiusUpperTail.NormalizedFrobeniusEnergy
import Mathlib.Logic.Equiv.Fin.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable def euclideanEntryMatrix (n : ℕ) :
    EuclideanSpace ℂ (Fin (n*n)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x i j := x (finProdFinEquiv (i,j))
  map_add' x y := by ext i j; rfl
  map_smul' a x := by ext i j; rfl

lemma euclideanEntryMatrix_norm (n : ℕ) (x : EuclideanSpace ℂ (Fin (n*n))) :
    ‖euclideanEntryMatrix n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [matrix_frobenius_sq_sum, EuclideanSpace.norm_sq_eq]
  change (∑ i, ∑ j, ‖x (finProdFinEquiv (i,j))‖^2) = ∑ k, ‖x k‖^2
  simpa only [Fintype.sum_prod_type] using finProdFinEquiv.sum_comp (fun k => ‖x k‖^2)

lemma euclideanEntryMatrix_norm_sub (n : ℕ) (x y : EuclideanSpace ℂ (Fin (n*n))) :
    ‖euclideanEntryMatrix n x-euclideanEntryMatrix n y‖ = ‖x-y‖ := by
  rw [← map_sub, euclideanEntryMatrix_norm]

noncomputable def euclideanResidualMatrix (n : ℕ) (z : ℂ)
    (x : EuclideanSpace ℂ (Fin (n*n))) : Matrix (Fin n) (Fin n) ℂ :=
  (1/Real.sqrt (n : ℝ)) • euclideanEntryMatrix n x-z • 1

lemma euclideanResidualMatrix_norm_sub (n : ℕ) (z : ℂ)
    (x y : EuclideanSpace ℂ (Fin (n*n))) :
    ‖euclideanResidualMatrix n z x-euclideanResidualMatrix n z y‖ =
      (1/Real.sqrt (n : ℝ))*‖x-y‖ := by
  unfold euclideanResidualMatrix
  rw [sub_sub_sub_cancel_right, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1/Real.sqrt (n : ℝ)),
    euclideanEntryMatrix_norm_sub]

lemma euclideanResidualMatrix_combination (n : ℕ) (z : ℂ)
    (x y : EuclideanSpace ℂ (Fin (n*n))) (a b : ℝ) (hab : a+b=1) :
    euclideanResidualMatrix n z (a • x+b • y) =
      a • euclideanResidualMatrix n z x+b • euclideanResidualMatrix n z y := by
  unfold euclideanResidualMatrix
  rw [map_add, map_smul, map_smul, smul_add, smul_sub, smul_sub]
  rw [smul_comm (1/Real.sqrt (n : ℝ)) a, smul_comm (1/Real.sqrt (n : ℝ)) b]
  have hz : a • (z • (1 : Matrix (Fin n) (Fin n) ℂ))+
      b • (z • (1 : Matrix (Fin n) (Fin n) ℂ)) = z • 1 := by rw [← add_smul, hab, one_smul]
  calc
    _ = (a • ((1/Real.sqrt (n : ℝ)) • euclideanEntryMatrix n x)+
      b • ((1/Real.sqrt (n : ℝ)) • euclideanEntryMatrix n y))-
      (a • (z • (1 : Matrix (Fin n) (Fin n) ℂ))+b • (z • 1)) := by rw [hz]
    _ = _ := by abel

#print axioms euclideanEntryMatrix_norm
#print axioms euclideanEntryMatrix_norm_sub
#print axioms euclideanResidualMatrix_norm_sub
#print axioms euclideanResidualMatrix_combination
end SpectralRadiusUpperTail
