import SpectralRadiusUpperTail.MatrixTracePowers
import SpectralRadiusUpperTail.MatrixTraceCauchySchwarz

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unrooted even Schatten moment, avoiding fractional-power conventions. -/
def matrixTraceMoment (n : ℕ) (A : Matrix ι ι 𝕂) : ℝ :=
  RCLike.re ((A*Aᴴ)^n).trace

lemma matrixTraceMoment_nonneg (n : ℕ) (A : Matrix ι ι 𝕂) :
    0 ≤ matrixTraceMoment n A := matrix_trace_gram_power_nonneg A n

lemma matrixTraceMoment_conjTranspose (n : ℕ) (A : Matrix ι ι 𝕂) :
    matrixTraceMoment n Aᴴ = matrixTraceMoment n A := by
  unfold matrixTraceMoment
  rw [Matrix.conjTranspose_conjTranspose, matrix_trace_product_power_cycle]

lemma matrixTraceMoment_gram (n : ℕ) (A : Matrix ι ι 𝕂) :
    matrixTraceMoment n (A*Aᴴ) = matrixTraceMoment (2*n) A := by
  unfold matrixTraceMoment
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← pow_two, ← pow_mul]

lemma matrixTraceMoment_product (n : ℕ) (A B : Matrix ι ι 𝕂) :
    matrixTraceMoment n (A*B) = RCLike.re ((Aᴴ*A*(B*Bᴴ))^n).trace := by
  unfold matrixTraceMoment
  rw [Matrix.conjTranspose_mul]
  have he : A*B*(Bᴴ*Aᴴ) = A*(B*Bᴴ)*Aᴴ := by simp only [Matrix.mul_assoc]
  rw [he, matrix_trace_sandwich_power]

lemma matrixTraceMoment_eq_norm (n : ℕ) (A : Matrix ι ι 𝕂) :
    matrixTraceMoment n A = ‖((A*Aᴴ)^n).trace‖ := by
  have h := ((Matrix.posSemidef_self_mul_conjTranspose A).pow n).trace_nonneg
  have hn := RCLike.norm_of_nonneg' h
  have hr := congrArg RCLike.re hn
  simpa [matrixTraceMoment] using hr.symm

#print axioms matrixTraceMoment_product
#print axioms matrixTraceMoment_eq_norm
end SpectralRadiusUpperTail
