import SpectralRadiusUpperTail.MatrixCoefficientDifference

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

noncomputable def matrixCoefficientLinear (p q : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun := matrixCoefficient p q
  map_add' := matrixCoefficient_add p q
  map_smul' := fun s A => matrixCoefficient_smul p q s A

noncomputable def matrixCoefficientCLM (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  (matrixCoefficientLinear p q).mkContinuous 1 (fun A => by
    rw [one_mul]
    exact matrixCoefficient_norm_le p q hp hq A)

@[simp] lemma matrixCoefficientCLM_apply (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (A : Matrix (Fin n) (Fin n) ℂ) : matrixCoefficientCLM p q hp hq A = matrixCoefficient p q A := rfl

#print axioms matrixCoefficientLinear
#print axioms matrixCoefficientCLM
#print axioms matrixCoefficientCLM_apply
end SpectralRadiusUpperTail
