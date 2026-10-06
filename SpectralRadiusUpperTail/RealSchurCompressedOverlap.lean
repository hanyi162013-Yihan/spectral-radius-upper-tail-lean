import SpectralRadiusUpperTail.RealSchurLowerCornerIntertwiner
import SpectralRadiusUpperTail.RealSchurMatrixSylvesterZero
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A block-upper intertwiner cannot mix later blocks into earlier
ones when every leading/trailing compressed pair has disjoint spectra. -/
theorem blockUpper_intertwiner_upper_of_compression_coprime
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T U X : Matrix ι ι ℝ)
    (hT : T.BlockTriangular b) (hU : U.BlockTriangular b)
    (hX : T*X=X*U)
    (hcop : ∀ k : β,
      let P := {i : ι // b i ≤ k}
      let C := {i : ι // k < b i}
      IsCoprime
        (U.submatrix (Subtype.val : P → ι) (Subtype.val : P → ι)).charpoly
        (T.submatrix (Subtype.val : C → ι) (Subtype.val : C → ι)).charpoly) :
    X.BlockTriangular b := by
  intro i j hij
  let k := b j
  let P := {z : ι // b z ≤ k}
  let C := {z : ι // k < b z}
  have hcorner :
      X.submatrix (Subtype.val : C → ι) (Subtype.val : P → ι) = 0 := by
    exact matrix_eq_zero_of_coprime_charpoly_intertwining
      (U.submatrix (Subtype.val : P → ι) (Subtype.val : P → ι))
      (T.submatrix (Subtype.val : C → ι) (Subtype.val : C → ι))
      (X.submatrix (Subtype.val : C → ι) (Subtype.val : P → ι))
      (hcop k) (blockUpper_intertwiner_lowerCorner b T U X hT hU hX k)
  have hentry := congrArg (fun M : Matrix C P ℝ =>
      M (⟨i,hij⟩ : C) (⟨j,le_rfl⟩ : P)) hcorner
  simpa only [Matrix.submatrix_apply, Matrix.zero_apply] using hentry

#print axioms blockUpper_intertwiner_upper_of_compression_coprime
end SpectralRadiusUpperTail
