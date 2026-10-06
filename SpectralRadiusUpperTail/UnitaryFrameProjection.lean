import SpectralRadiusUpperTail.UnitaryColumnFrame

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

lemma matrix_frame_projection (M : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) :
    M.submatrix id (fun i : s => (i : Fin n)) *
      (M.submatrix id (fun i : s => (i : Fin n)))ᴴ =
    M*Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)*Mᴴ := by
  classical
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply]
  simp only [Matrix.submatrix_apply,Matrix.conjTranspose_apply,Matrix.mul_diagonal,id_eq]
  trans ∑ k ∈ s, M i k * star (M j k)
  · exact Finset.sum_coe_sort s (fun k => M i k * star (M j k))
  · simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
    rw [← Finset.sum_filter]
    simp

lemma unitary_frame_projection (U : Matrix.unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    (U : Matrix (Fin n) (Fin n) ℂ).submatrix id (fun i : s => (i : Fin n)) *
      ((U : Matrix (Fin n) (Fin n) ℂ).submatrix id (fun i : s => (i : Fin n)))ᴴ =
    (U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)*
      (star U : Matrix (Fin n) (Fin n) ℂ) := by
  exact matrix_frame_projection (U : Matrix (Fin n) (Fin n) ℂ) s

lemma unitary_frame_factorization (D : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    D*((U : Matrix (Fin n) (Fin n) ℂ).submatrix id (fun i : s => (i : Fin n)))*
      ((U : Matrix (Fin n) (Fin n) ℂ).submatrix id (fun i : s => (i : Fin n)))ᴴ =
    D*(U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)*
      (star U : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.mul_assoc,unitary_frame_projection]
  simp only [Matrix.mul_assoc]

#print axioms matrix_frame_projection
#print axioms unitary_frame_projection
#print axioms unitary_frame_factorization
end SpectralRadiusUpperTail
