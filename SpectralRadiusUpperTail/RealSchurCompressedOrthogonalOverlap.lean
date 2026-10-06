import SpectralRadiusUpperTail.RealSchurCompressedOverlap
import SpectralRadiusUpperTail.RealSchurBlockOrthogonalRigidity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Ordered orthogonal Schur frames differ only by rotations within
blocks, provided the leading compressed blocks of the second
representation are spectrally disjoint from the trailing compressed
blocks of the first. -/
theorem realSchurCompressedOrthogonalOverlap_offBlock
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (A Q R T U : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hAQ : A=Q*T*Qᵀ) (hAR : A=R*U*Rᵀ)
    (hcop : ∀ k : β,
      let P := {i : ι // b i ≤ k}
      let C := {i : ι // k < b i}
      IsCoprime
        (U.submatrix (Subtype.val : P → ι) (Subtype.val : P → ι)).charpoly
        (T.submatrix (Subtype.val : C → ι) (Subtype.val : C → ι)).charpoly)
    (i j : ι) (hij : b i ≠ b j) :
    (Qᵀ*R) i j = 0 := by
  have hleft : Qᵀ*A*R = T*(Qᵀ*R) := by
    rw [hAQ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul]
  have hright : Qᵀ*A*R = (Qᵀ*R)*U := by
    rw [hAR]
    simp only [Matrix.mul_assoc]
    rw [hR]
    simp
  have hinter : T*(Qᵀ*R)=(Qᵀ*R)*U :=
    hleft.symm.trans hright
  have hQR : (Qᵀ*R)ᵀ*(Qᵀ*R)=1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      (Rᵀ*Q)*(Qᵀ*R) = Rᵀ*(Q*Qᵀ)*R := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_eq_one_comm.mp hQ, Matrix.mul_one, hR]
  exact orthogonal_blockTriangular_offBlock b (Qᵀ*R) hQR
    (blockUpper_intertwiner_upper_of_compression_coprime
      b T U (Qᵀ*R) hT hU hinter hcop) i j hij

#print axioms realSchurCompressedOrthogonalOverlap_offBlock
end SpectralRadiusUpperTail
