import SpectralRadiusUpperTail.MatrixTraceMoments
import SpectralRadiusUpperTail.ListPairProducts

namespace SpectralRadiusUpperTail
open scoped ComplexOrder Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unrooted 2m-factor trace Holder assertion used in the induction. -/
def MatrixTraceHolder (𝕂 : Type*) [RCLike 𝕂] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (m : ℕ) : Prop :=
  ∀ L : List (Matrix ι ι 𝕂), L.length = 2*m →
    ‖L.prod.trace‖^(2*m) ≤ (L.map (matrixTraceMoment m)).prod

lemma matrix_trace_holder_one : MatrixTraceHolder 𝕂 ι 1 := by
  intro L hL
  obtain ⟨A,B,rfl⟩ := List.length_eq_two.mp (by simpa using hL)
  simpa only [List.prod_cons, List.prod_nil, List.map_cons, List.map_nil,
    mul_one, matrixTraceMoment, pow_one] using matrix_trace_product_cauchy_schwarz A B

lemma matrixTraceMoment_product_norm (m : ℕ) (A B : Matrix ι ι 𝕂) :
    matrixTraceMoment m (A*B) = ‖((Aᴴ*A*(B*Bᴴ))^m).trace‖ := by
  rw [matrixTraceMoment_eq_norm, Matrix.conjTranspose_mul]
  have he : A*B*(Bᴴ*Aᴴ) = A*(B*Bᴴ)*Aᴴ := by simp only [Matrix.mul_assoc]
  rw [he, matrix_trace_sandwich_power]

/-- Derive the product-moment estimate from the preceding Holder order.
This is an induction step, not a hypothesis substituted for the final theorem. -/
lemma matrix_trace_holder_product_step {m : ℕ} (hm : 0 < m)
    (h : MatrixTraceHolder 𝕂 ι m) (A B : Matrix ι ι 𝕂) :
    (matrixTraceMoment m (A*B))^2 ≤
      matrixTraceMoment (2*m) A*matrixTraceMoment (2*m) B := by
  let P := List.replicate m (Aᴴ*A,B*Bᴴ)
  have hlen : (pairedList P).length = 2*m := by simp [P,pairedList_length]
  have hh := h (pairedList P) hlen
  rw [pairedList_prod, pairedList_map_prod] at hh
  simp only [P, List.map_replicate, List.prod_replicate] at hh
  have hA : matrixTraceMoment m (Aᴴ*A) = matrixTraceMoment (2*m) A := by
    simpa only [Matrix.conjTranspose_conjTranspose, matrixTraceMoment_conjTranspose] using
      matrixTraceMoment_gram m Aᴴ
  rw [hA, matrixTraceMoment_gram, ← matrixTraceMoment_product_norm] at hh
  apply (pow_le_pow_iff_left₀ (sq_nonneg _) (mul_nonneg
    (matrixTraceMoment_nonneg _ _) (matrixTraceMoment_nonneg _ _)) hm.ne').mp
  simpa only [← pow_mul] using hh

#print axioms matrix_trace_holder_one
#print axioms matrix_trace_holder_product_step
end SpectralRadiusUpperTail
