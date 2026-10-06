import SpectralRadiusUpperTail.MatrixTraceHolderDyadic

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Repetition in the proved dyadic Holder inequality bounds a matrix power. -/
theorem matrix_trace_dyadic_power_norm (A : Matrix ι ι 𝕂) (k : ℕ) :
    ‖(A^(2*(2^k))).trace‖ ≤ matrixTraceMoment (2^k) A := by
  have h := matrix_trace_dyadic_list_bound k (List.replicate (2*(2^k)) A) (by simp)
  simp only [List.prod_replicate,List.map_replicate] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (matrixTraceMoment_nonneg _ _)
    (by positivity : 2*(2^k) ≠ 0)).mp h

/-- The dyadic trace inequality needed before taking the Lie-product limit. -/
theorem matrix_trace_hermitian_dyadic (A B : Matrix ι ι 𝕂)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : ℕ) :
    RCLike.re ((A*B)^(2^k)).trace ≤ RCLike.re (A^(2^k)*B^(2^k)).trace := by
  induction k generalizing A B with
  | zero => simp
  | succ k ih =>
    have hnorm := matrix_trace_dyadic_power_norm (A*B) k
    have hm : matrixTraceMoment (2^k) (A*B) =
        RCLike.re ((A^2*B^2)^(2^k)).trace := by
      rw [matrixTraceMoment_product,hA.eq,hB.eq,pow_two,pow_two]
    rw [hm] at hnorm
    have ht := (RCLike.re_le_norm _).trans hnorm
    have hi := ih (A^2) (B^2) (hA.pow 2) (hB.pow 2)
    have hh := ht.trans hi
    have he : 2^(k+1) = 2*(2^k) := by rw [pow_succ,Nat.mul_comm]
    rw [he]
    simpa only [← pow_mul] using hh

#print axioms matrix_trace_dyadic_power_norm
#print axioms matrix_trace_hermitian_dyadic
end SpectralRadiusUpperTail
