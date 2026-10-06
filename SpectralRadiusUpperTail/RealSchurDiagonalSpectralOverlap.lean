import SpectralRadiusUpperTail.RealSchurOrderedSpectralOverlap
import SpectralRadiusUpperTail.RealSchurPrefixBlockCharpoly
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Matching diagonal-block characteristic polynomials imply matching
characteristic polynomials on every ordered prefix. -/
theorem blockUpper_prefix_charpoly_eq_of_diagonalBlock_eq
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T U : Matrix ι ι ℝ)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hdiag : ∀ a : β,
      (U.toSquareBlock b a).charpoly =
        (T.toSquareBlock b a).charpoly)
    (k : β) :
    (U.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
      (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly =
    (T.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
      (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly := by
  rw [blockUpper_prefix_charpoly_product b U hU k,
    blockUpper_prefix_charpoly_product b T hT k]
  simp_rw [hdiag]

/-- Two simple-spectrum real Schur representations with the same
ordered diagonal-block spectra can differ only by orthogonal changes
of basis inside the individual blocks. -/
theorem realSchurDiagonalSpectralOverlap_offBlock
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (A Q R T U : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hAQ : A=Q*T*Qᵀ) (hAR : A=R*U*Rᵀ)
    (hsep : T.charpoly.Separable)
    (hdiag : ∀ a : β,
      (U.toSquareBlock b a).charpoly =
        (T.toSquareBlock b a).charpoly)
    (i j : ι) (hij : b i ≠ b j) :
    (Qᵀ*R) i j = 0 := by
  exact realSchurOrderedSpectralOverlap_offBlock
    b A Q R T U hQ hR hT hU hAQ hAR hsep
    (blockUpper_prefix_charpoly_eq_of_diagonalBlock_eq b T U hT hU hdiag)
    i j hij

#print axioms blockUpper_prefix_charpoly_eq_of_diagonalBlock_eq
#print axioms realSchurDiagonalSpectralOverlap_offBlock
end SpectralRadiusUpperTail
