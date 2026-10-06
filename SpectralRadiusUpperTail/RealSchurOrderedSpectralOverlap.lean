import SpectralRadiusUpperTail.RealSchurCompressedOrthogonalOverlap
import SpectralRadiusUpperTail.RealSchurCompressionCoprime
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- For a simple-spectrum matrix, two orthogonal block-upper Schur
representations with the same characteristic polynomial at each
ordered block prefix have a block-diagonal relative frame. -/
theorem realSchurOrderedSpectralOverlap_offBlock
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (A Q R T U : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hAQ : A=Q*T*Qᵀ) (hAR : A=R*U*Rᵀ)
    (hsep : T.charpoly.Separable)
    (hprefix : ∀ k : β,
      (U.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
        (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly =
      (T.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
        (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly)
    (i j : ι) (hij : b i ≠ b j) :
    (Qᵀ*R) i j = 0 := by
  apply realSchurCompressedOrthogonalOverlap_offBlock
    b A Q R T U hQ hR hT hU hAQ hAR ?_ i j hij
  intro k
  exact blockUpper_cross_compression_coprime b T U hT hsep k (hprefix k)

#print axioms realSchurOrderedSpectralOverlap_offBlock
end SpectralRadiusUpperTail
