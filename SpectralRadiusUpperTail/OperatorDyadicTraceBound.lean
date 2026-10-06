import SpectralRadiusUpperTail.FrobeniusTraceIdentity

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

/-- Dyadic trace moments suffice for operator-norm Markov bounds. -/
lemma operator_norm_dyadic_le_trace (A : Matrix (Fin N) (Fin N) 𝕂) (k : ℕ) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := 𝕂) A‖^(2*(2^(k+1))) ≤
      matrixTraceMoment (2^(k+1)) A := by
  let H := A*Aᴴ
  have hH : IsSelfAdjoint H := by
    change Hᴴ = H
    simp only [H, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hnorm : ‖H‖ = ‖A‖^2 := by
    have hh := Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,pow_two] using hh
  have ht := euclidean_operator_norm_sq_le_trace (H^(2^k))
  rw [Matrix.l2_opNorm_toEuclideanCLM,hH.norm_pow_two_pow,hnorm] at ht
  have he : (H^(2^k) * (H^(2^k))ᴴ) = H^(2^(k+1)) := by
    rw [Matrix.conjTranspose_pow]
    have hh : Hᴴ = H := hH
    rw [hh, ← pow_add]
    congr 1
    omega
  rw [he] at ht
  change ‖A‖^(2*(2^(k+1))) ≤ _
  convert ht using 1
  · simp only [← pow_mul]
    congr 1
    rw [pow_succ]
    omega
  · rfl

#print axioms operator_norm_dyadic_le_trace
end SpectralRadiusUpperTail
