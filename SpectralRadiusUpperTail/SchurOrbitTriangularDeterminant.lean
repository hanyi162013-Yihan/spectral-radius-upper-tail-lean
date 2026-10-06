import SpectralRadiusUpperTail.RealSchurGlobalScalarOrbitDiagonal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A finite matrix whose distinct fibers are triangular and whose entries
within each fiber are diagonal has determinant equal to the product of its
diagonal entries. This is the algebraic determinant step in the Schur orbit
Jacobian; the geometry of the orbit chart is a separate issue. -/
theorem determinant_of_block_triangular_fiber_diagonal
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [LinearOrder α]
    (M : Matrix ι ι ℝ) (b : ι → α)
    (htri : M.BlockTriangular b)
    (hfiber : ∀ i j : ι, b i = b j → i ≠ j → M i j = 0) :
    M.det = ∏ i, M i i := by
  classical
  have hblock (k : α) :
      M.toSquareBlock b k = Matrix.diagonal (fun i : {i // b i = k} => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.toSquareBlock_def]
    · have hij' : (i : ι) ≠ j := by
        intro heq
        exact hij (Subtype.ext heq)
      have hzero : M i j = 0 :=
        hfiber i j (i.property.trans j.property.symm) hij'
      simp [Matrix.toSquareBlock_def, hij, hzero]
  calc
    M.det = ∏ k : α, (M.toSquareBlock b k).det := htri.det_fintype
    _ = ∏ k : α, ∏ i : {i // b i = k}, M i i := by
      simp_rw [hblock, Matrix.det_diagonal]
    _ = ∏ i : ι, M i i := Fintype.prod_fiberwise b (fun i => M i i)

#print axioms determinant_of_block_triangular_fiber_diagonal
end SpectralRadiusUpperTail
