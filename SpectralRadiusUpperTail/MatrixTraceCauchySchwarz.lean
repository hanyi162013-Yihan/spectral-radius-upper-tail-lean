import Mathlib.Analysis.Matrix.Order

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Trace Cauchy--Schwarz, using the actual matrix inner product induced by I. -/
theorem matrix_trace_cauchy_schwarz (A B : Matrix ι ι 𝕂) :
    ‖(A*Bᴴ).trace‖^2 ≤
      RCLike.re (A*Aᴴ).trace * RCLike.re (B*Bᴴ).trace := by
  let := Matrix.toMatrixSeminormedAddCommGroup (1 : Matrix ι ι 𝕂)
    Matrix.PosSemidef.one
  let := Matrix.toMatrixInnerProductSpace (1 : Matrix ι ι 𝕂)
    Matrix.PosSemidef.one
  have h := pow_le_pow_left₀ (norm_nonneg (inner 𝕂 B A)) (norm_inner_le_norm B A) 2
  have hA : ‖A‖^2 = RCLike.re (A*Aᴴ).trace := by
    have hh := norm_sq_eq_re_inner (𝕜 := 𝕂) A
    change ‖A‖^2 = RCLike.re (A*1*Aᴴ).trace at hh
    simpa only [Matrix.mul_one] using hh
  have hB : ‖B‖^2 = RCLike.re (B*Bᴴ).trace := by
    have hh := norm_sq_eq_re_inner (𝕜 := 𝕂) B
    change ‖B‖^2 = RCLike.re (B*1*Bᴴ).trace at hh
    simpa only [Matrix.mul_one] using hh
  rw [mul_pow, hB, hA] at h
  change ‖(A*1*Bᴴ).trace‖^2 ≤ _ at h
  simpa only [Matrix.mul_one, mul_comm] using h

/-- Product form, with no Hermitian or commuting assumptions. -/
theorem matrix_trace_product_cauchy_schwarz (A B : Matrix ι ι 𝕂) :
    ‖(A*B).trace‖^2 ≤
      RCLike.re (A*Aᴴ).trace * RCLike.re (B*Bᴴ).trace := by
  have h := matrix_trace_cauchy_schwarz A Bᴴ
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm Bᴴ B] using h

#print axioms matrix_trace_cauchy_schwarz
#print axioms matrix_trace_product_cauchy_schwarz
end SpectralRadiusUpperTail
