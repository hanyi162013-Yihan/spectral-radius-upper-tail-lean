import SpectralRadiusUpperTail.ActualMatrixIdentity
import SpectralRadiusUpperTail.MatrixSqrtEnergy

namespace SpectralRadiusUpperTail
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

noncomputable def spectralResidualGram (x : Fin n → Fin n → 𝕂) (b : 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  (normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).conjTranspose *
    (normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂))

lemma spectralResidualGram_posSemidef (x : Fin n → Fin n → 𝕂) (b : 𝕂) :
    (spectralResidualGram x b).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _

lemma matrix_gram_energy (A : Matrix (Fin n) (Fin n) 𝕂) (v : EuclideanSpace 𝕂 (Fin n)) :
    RCLike.re (inner 𝕂 v (Matrix.toEuclideanCLM (𝕜 := 𝕂) (A.conjTranspose*A) v)) =
      ‖Matrix.toEuclideanCLM (𝕜 := 𝕂) A v‖^2 := by
  have he := ContinuousLinearMap.adjoint_inner_right (Matrix.toEuclideanCLM (𝕜 := 𝕂) A)
    v (Matrix.toEuclideanCLM (𝕜 := 𝕂) A v)
  change inner 𝕂 v ((star (Matrix.toEuclideanCLM (𝕜 := 𝕂) A))
    (Matrix.toEuclideanCLM (𝕜 := 𝕂) A v)) = _ at he
  rw [← map_star,← ContinuousLinearMap.comp_apply,← ContinuousLinearMap.mul_def,← map_mul] at he
  have hh := congrArg RCLike.re he
  simpa only [Matrix.star_eq_conjTranspose,inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow,RCLike.ofReal_re] using hh

#print axioms spectralResidualGram
#print axioms spectralResidualGram_posSemidef
#print axioms matrix_gram_energy
end SpectralRadiusUpperTail
