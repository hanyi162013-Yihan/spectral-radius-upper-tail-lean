import Mathlib.Analysis.Matrix.Order

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_product_power_shuffle (A B : Matrix ι ι 𝕂) (n : ℕ) :
    (A*B)^n*A = A*(B*A)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    calc
      _ = ((A*B)^n*A)*(B*A) := by simp only [Matrix.mul_assoc]
      _ = (A*(B*A)^n)*(B*A) := by rw [ih]
      _ = _ := by rw [Matrix.mul_assoc]

lemma matrix_trace_product_power_cycle (A B : Matrix ι ι 𝕂) (n : ℕ) :
    ((A*B)^n).trace = ((B*A)^n).trace := by
  cases n with
  | zero => simp
  | succ n =>
    rw [pow_succ, ← Matrix.mul_assoc, matrix_product_power_shuffle,
      Matrix.trace_mul_cycle, ← pow_succ']

/-- Cyclic rearrangement needed for the Schatten product-moment induction. -/
lemma matrix_trace_sandwich_power (A B : Matrix ι ι 𝕂) (n : ℕ) :
    ((A*B*Aᴴ)^n).trace = ((Aᴴ*A*B)^n).trace := by
  rw [matrix_trace_product_power_cycle, Matrix.mul_assoc]

lemma matrix_trace_gram_power_nonneg (A : Matrix ι ι 𝕂) (n : ℕ) :
    0 ≤ RCLike.re ((A*Aᴴ)^n).trace := by
  have h : (A*Aᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  exact (RCLike.nonneg_iff.mp (h.pow n).trace_nonneg).1

#print axioms matrix_trace_product_power_cycle
#print axioms matrix_trace_sandwich_power
#print axioms matrix_trace_gram_power_nonneg
end SpectralRadiusUpperTail
