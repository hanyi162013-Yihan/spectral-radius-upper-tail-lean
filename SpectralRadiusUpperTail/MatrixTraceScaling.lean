import SpectralRadiusUpperTail.MatrixTraceMoments
import Mathlib.Algebra.Algebra.Operations

namespace SpectralRadiusUpperTail
open scoped Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixTraceMoment_smul (A : Matrix ι ι 𝕂) (s : 𝕂) (q : ℕ) :
    matrixTraceMoment q (s • A) = ‖s‖^(2*q) * matrixTraceMoment q A := by
  rw [matrixTraceMoment_eq_norm,matrixTraceMoment_eq_norm]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul,smul_pow,Matrix.trace_smul,norm_smul,norm_pow,norm_mul,norm_star]
  rw [← pow_two, ← pow_mul]

lemma normalized_matrixTraceMoment_power {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕂)
    (m q : ℕ) :
    matrixTraceMoment q ((((1/Real.sqrt (n : ℝ) : ℝ) : 𝕂) • A)^m) =
      (1/(n : ℝ))^(q*m) * matrixTraceMoment q (A^m) := by
  rw [smul_pow,matrixTraceMoment_smul]
  simp only [norm_pow,RCLike.norm_ofReal]
  have he : (|1/Real.sqrt (n : ℝ)|^m)^(2*q) = (1/(n : ℝ))^(q*m) := by
    rw [← pow_mul]
    have hx : m*(2*q)=2*(q*m) := by ring
    rw [hx,pow_mul,sq_abs,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [he]

#print axioms matrixTraceMoment_smul
#print axioms normalized_matrixTraceMoment_power
end SpectralRadiusUpperTail
