import SpectralRadiusUpperTail.HermitianDilation
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace SpectralRadiusUpperTail
open Matrix WithLp
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

lemma euclidean_sum_right_norm (x : EuclideanSpace 𝕂 (Fin N)) :
    ‖toLp 2 (Sum.elim (0 : Fin N → 𝕂) (ofLp x))‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

lemma euclidean_sum_left_norm (x : EuclideanSpace 𝕂 (Fin N)) :
    ‖toLp 2 (Sum.elim (ofLp x) (0 : Fin N → 𝕂))‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

/-- The original Euclidean operator norm is controlled by its actual
Hermitian dilation, giving the required direction of probability transfer. -/
theorem euclidean_operator_le_hermitianDilation (A : Matrix (Fin N) (Fin N) 𝕂) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) A‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂) (hermitianDilation A)‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) A
  let H := Matrix.toEuclideanCLM (n := Fin N ⊕ Fin N) (𝕜 := 𝕂) (hermitianDilation A)
  apply T.opNorm_le_bound (norm_nonneg H)
  intro x
  let y : EuclideanSpace 𝕂 (Fin N ⊕ Fin N) := toLp 2 (Sum.elim (0 : Fin N → 𝕂) (ofLp x))
  have hy : ‖y‖ = ‖x‖ := euclidean_sum_right_norm x
  have hact : H y = toLp 2 (Sum.elim (ofLp (T x)) (0 : Fin N → 𝕂)) := by
    change toLp 2 ((hermitianDilation A).mulVec (Sum.elim (0 : Fin N → 𝕂) (ofLp x))) = _
    unfold hermitianDilation
    rw [Matrix.fromBlocks_mulVec]
    congr 1
    funext p
    cases p <;> simp [Function.comp_def, Matrix.ofLp_toEuclideanCLM, T, Matrix.mulVec, dotProduct]
  calc
    ‖T x‖ = ‖H y‖ := by rw [hact, euclidean_sum_left_norm]
    _ ≤ ‖H‖*‖y‖ := H.le_opNorm y
    _ = ‖H‖*‖x‖ := by rw [hy]

#print axioms euclidean_operator_le_hermitianDilation
end SpectralRadiusUpperTail
