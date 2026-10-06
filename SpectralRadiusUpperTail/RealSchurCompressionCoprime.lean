import SpectralRadiusUpperTail.RealSchurCompressionCharpoly
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- For a simple-spectrum block-upper matrix, matching the leading
compressed characteristic polynomial of a second representation is
enough to obtain the cross-block spectral separation needed for
ordered-frame uniqueness. -/
theorem blockUpper_cross_compression_coprime
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T U : Matrix ι ι ℝ)
    (hT : T.BlockTriangular b) (hsep : T.charpoly.Separable)
    (k : β)
    (hprefix :
      (U.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
        (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly =
      (T.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
        (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly) :
    IsCoprime
      (U.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
        (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly
      (T.submatrix (Subtype.val : {i : ι // k < b i} → ι)
        (Subtype.val : {i : ι // k < b i} → ι)).charpoly := by
  have hfac := blockUpper_charpoly_prefix_suffix b T hT k
  have hsepProd :
      ((T.submatrix (Subtype.val : {i : ι // b i ≤ k} → ι)
        (Subtype.val : {i : ι // b i ≤ k} → ι)).charpoly *
      (T.submatrix (Subtype.val : {i : ι // k < b i} → ι)
        (Subtype.val : {i : ι // k < b i} → ι)).charpoly).Separable := by
    rw [← hfac]
    exact hsep
  rw [hprefix]
  exact hsepProd.isCoprime

#print axioms blockUpper_cross_compression_coprime
end SpectralRadiusUpperTail
