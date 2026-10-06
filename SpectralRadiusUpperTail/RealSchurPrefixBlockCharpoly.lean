import SpectralRadiusUpperTail.RealSchurCompressionCharpoly
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Restricting a block-upper matrix to a prefix does not change any
diagonal block completely contained in that prefix. -/
theorem blockUpper_prefix_diagonalBlock_charpoly
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T : Matrix ι ι ℝ) (k a : β) (ha : a ≤ k) :
    let P := {i : ι // b i ≤ k}
    ((T.submatrix (Subtype.val : P → ι) (Subtype.val : P → ι)).toSquareBlock
      (fun z : P => b z) a).charpoly =
    (T.toSquareBlock b a).charpoly := by
  classical
  dsimp only
  let P := {i : ι // b i ≤ k}
  let e : {z : ι // b z = a} ≃ {z : P // b z = a} := {
    toFun := fun z => ⟨⟨z.1, by change b z.1 ≤ k; rw [z.2]; exact ha⟩, z.2⟩
    invFun := fun z => ⟨z.1.1, z.2⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
  }
  have hm : Matrix.reindex e e (T.toSquareBlock b a) =
      (T.submatrix (Subtype.val : P → ι) (Subtype.val : P → ι)).toSquareBlock
        (fun z : P => b z) a := by
    ext i j
    rfl
  rw [← hm, Matrix.charpoly_reindex]

/-- The prefix compression's characteristic polynomial is exactly the
product of the characteristic polynomials of its diagonal blocks. -/
theorem blockUpper_prefix_charpoly_product
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (T : Matrix ι ι ℝ)
    (hT : T.BlockTriangular b) (k : β) :
    let P := {i : ι // b i ≤ k}
    (T.submatrix (Subtype.val : P → ι)
      (Subtype.val : P → ι)).charpoly =
    ∏ a ∈ Finset.univ.image (fun z : P => b z),
      (T.toSquareBlock b a).charpoly := by
  classical
  dsimp only
  let P := {i : ι // b i ≤ k}
  have hcomp : (T.submatrix (Subtype.val : P → ι)
      (Subtype.val : P → ι)).BlockTriangular (fun z : P => b z) := by
    intro i j hij
    exact hT hij
  rw [hcomp.charpoly]
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp ha
  exact blockUpper_prefix_diagonalBlock_charpoly b T k (b z) z.property

#print axioms blockUpper_prefix_diagonalBlock_charpoly
#print axioms blockUpper_prefix_charpoly_product
end SpectralRadiusUpperTail
