import SpectralRadiusUpperTail.MatrixTraceMoments

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first nontrivial product-moment step for dyadic trace Holder. -/
theorem matrixTraceMoment_product_sq (A B : Matrix ι ι 𝕂) :
    (matrixTraceMoment 1 (A*B))^2 ≤ matrixTraceMoment 2 A*matrixTraceMoment 2 B := by
  have he : ((A*B)*(A*B)ᴴ).trace = (Aᴴ*A*(B*Bᴴ)).trace := by
    rw [Matrix.conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A*B) Bᴴ Aᴴ
  have hc := matrix_trace_product_cauchy_schwarz (Aᴴ*A) (B*Bᴴ)
  have hm : RCLike.re ((Aᴴ*A)*(Aᴴ*A)ᴴ).trace = matrixTraceMoment 2 A := by
    have hh := matrixTraceMoment_gram 1 Aᴴ
    have hs : matrixTraceMoment 1 (Aᴴ*A) = matrixTraceMoment 2 A := by
      simpa only [Matrix.conjTranspose_conjTranspose, mul_one,
        matrixTraceMoment_conjTranspose] using hh
    simpa only [matrixTraceMoment, pow_one] using hs
  have hmB : RCLike.re ((B*Bᴴ)*(B*Bᴴ)ᴴ).trace = matrixTraceMoment 2 B := by
    have hs : matrixTraceMoment 1 (B*Bᴴ) = matrixTraceMoment 2 B := by
      simpa only [mul_one] using matrixTraceMoment_gram 1 B
    simpa only [matrixTraceMoment, pow_one] using hs
  rw [hm,hmB] at hc
  rw [matrixTraceMoment_eq_norm, pow_one, he]
  exact hc

/-- Four-factor trace Holder inequality in unrooted form.
All matrices are arbitrary; no commutation or Hermitian hypothesis is used. -/
theorem matrix_trace_four_holder (A B C D : Matrix ι ι 𝕂) :
    ‖(A*B*C*D).trace‖^4 ≤
      matrixTraceMoment 2 A*matrixTraceMoment 2 B*
        (matrixTraceMoment 2 C*matrixTraceMoment 2 D) := by
  have hc : ‖(A*B*(C*D)).trace‖^2 ≤
      matrixTraceMoment 1 (A*B)*matrixTraceMoment 1 (C*D) := by
    simpa only [matrixTraceMoment, pow_one] using
      matrix_trace_product_cauchy_schwarz (A*B) (C*D)
  have hs := pow_le_pow_left₀ (sq_nonneg ‖(A*B*(C*D)).trace‖) hc 2
  have hp := mul_le_mul (matrixTraceMoment_product_sq A B)
    (matrixTraceMoment_product_sq C D) (sq_nonneg _) (by
      exact mul_nonneg (matrixTraceMoment_nonneg 2 A) (matrixTraceMoment_nonneg 2 B))
  rw [mul_pow] at hs
  have hh := hs.trans hp
  simpa only [← pow_mul, Nat.reduceMul, Matrix.mul_assoc] using hh

#print axioms matrixTraceMoment_product_sq
#print axioms matrix_trace_four_holder
end SpectralRadiusUpperTail
