import SpectralRadiusUpperTail.RealSchurMixedCodeClassConnected

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem realSchurMixedCodeClass_orthogonal_forward
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (P : RealSchurMixedOrthogonalFrame s)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hA : A ∈ realSchurMixedCodeClass s code) :
    P.val*A*P.valᵀ ∈ realSchurMixedCodeClass s code := by
  obtain ⟨Q,T,hT,hsep,hcode,hrep⟩ := hA
  have hPQ : (P.val*Q.val)ᵀ*(P.val*Q.val)=1 := by
    calc
      _ = Q.valᵀ*(P.valᵀ*P.val)*Q.val := by
        simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [P.property,Matrix.mul_one,Q.property]
  refine ⟨⟨P.val*Q.val,hPQ⟩,T,hT,hsep,hcode,?_⟩
  rw [hrep]
  simp only [Matrix.transpose_mul,Matrix.mul_assoc]

/-- Spectral-code existence is invariant under every orthogonal change
of coordinates, independently of the chosen angle atlas. -/
theorem realSchurMixedCodeClass_orthogonal_iff
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (P : RealSchurMixedOrthogonalFrame s)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    P.val*A*P.valᵀ ∈ realSchurMixedCodeClass s code ↔ A ∈ realSchurMixedCodeClass s code := by
  refine ⟨?_,realSchurMixedCodeClass_orthogonal_forward s code P A⟩
  intro hA
  let Q : RealSchurMixedOrthogonalFrame s :=
    ⟨P.valᵀ,by simpa only [Matrix.transpose_transpose] using mul_eq_one_comm.mp P.property⟩
  have h := realSchurMixedCodeClass_orthogonal_forward s code Q _ hA
  have hcancel : Q.val*(P.val*A*P.valᵀ)*Q.valᵀ=A := by
    change P.valᵀ*(P.val*A*P.valᵀ)*(P.valᵀ)ᵀ=A
    rw [Matrix.transpose_transpose]
    calc
      _ = (P.valᵀ*P.val)*A*(P.valᵀ*P.val) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [P.property,Matrix.one_mul,Matrix.mul_one]
  simpa only [hcancel] using h

#print axioms realSchurMixedCodeClass_orthogonal_forward
#print axioms realSchurMixedCodeClass_orthogonal_iff
end SpectralRadiusUpperTail
