import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace SpectralRadiusUpperTail
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped MatrixOrder
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma matrix_sqrt_energy (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef)
    (x : EuclideanSpace 𝕂 (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n) (CFC.sqrt H) x‖^2 =
      RCLike.re (inner 𝕂 x (Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n) H x)) := by
  have hs : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n) (CFC.sqrt H)) :=
    (CFC.sqrt_nonneg H).isSelfAdjoint.map _
  have he := ContinuousLinearMap.adjoint_inner_right (Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n) (CFC.sqrt H))
    x (Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n) (CFC.sqrt H) x)
  rw [hs.adjoint_eq,← ContinuousLinearMap.comp_apply,← ContinuousLinearMap.mul_def,
    ← map_mul,CFC.sqrt_mul_sqrt_self _ hH.nonneg] at he
  have hh := congrArg RCLike.re he
  simpa only [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow,RCLike.ofReal_re] using hh.symm

#print axioms matrix_sqrt_energy
end SpectralRadiusUpperTail
