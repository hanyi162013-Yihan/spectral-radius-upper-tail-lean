import SpectralRadiusUpperTail.MatrixSqrtEnergy
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma matrix_regularized_posDef (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef)
    (s : ℝ) (hs : 0 < s) : (H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).PosDef := by
  apply Matrix.PosDef.posSemidef_add hH
  exact Matrix.PosDef.one.smul (by exact_mod_cast hs : (0 : 𝕂) < (s : 𝕂))

lemma matrix_quadratic_scale_shift (H : Matrix (Fin n) (Fin n) 𝕂) (c s : ℝ)
    (x : EuclideanSpace 𝕂 (Fin n)) :
    RCLike.re (inner 𝕂 x (Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n)
      ((c : 𝕂) • (H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂))) x)) =
      c*(RCLike.re (inner 𝕂 x (Matrix.toEuclideanCLM (𝕜 := 𝕂) (n := Fin n) H x))+s*‖x‖^2) := by
  simp only [map_smul,map_add,map_one,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,inner_smul_right,inner_add_right,inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow,RCLike.mul_re,map_add,RCLike.ofReal_re,RCLike.ofReal_im,
    zero_mul,sub_zero]

#print axioms matrix_regularized_posDef
#print axioms matrix_quadratic_scale_shift
end SpectralRadiusUpperTail
