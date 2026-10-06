import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- The explicit Householder matrix; its denominator will be positive
for the stereographic vector with leading coordinate one. -/
noncomputable def realRankOneReflection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) : Matrix ι ι ℝ :=
  1 - (2/(v ⬝ᵥ v)) • Matrix.vecMulVec v v

theorem realRankOneReflection_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) : (realRankOneReflection v)ᵀ = realRankOneReflection v := by
  simp only [realRankOneReflection, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_vecMulVec]

theorem realRankOneReflection_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (hv : v ⬝ᵥ v ≠ 0) :
    (realRankOneReflection v)ᵀ * realRankOneReflection v = 1 := by
  rw [realRankOneReflection_transpose]
  unfold realRankOneReflection
  simp only [Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp [hv]
  <;> ring

#print axioms realRankOneReflection_transpose
#print axioms realRankOneReflection_orthogonal
end SpectralRadiusUpperTail
