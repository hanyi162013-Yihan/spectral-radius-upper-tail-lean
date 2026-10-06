import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- At a marked real eigenline, order the spectral parameter before the
sphere tangent variables. The derivative has this block form: the upper
row is arbitrary, while the lower block is the shifted complementary
matrix. Its Jacobian is independent of the upper row. -/
theorem marked_real_eigenline_block_jacobian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (u : Matrix (Fin 1) ι ℝ)
    (x : ℝ) :
    (Matrix.fromBlocks
      (fun _ _ : Fin 1 => (-1 : ℝ)) u 0 (H - x • 1)).det =
      -(H - x • 1).det := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => -1
  change (Matrix.fromBlocks A u 0 (H - x • 1)).det = _
  rw [Matrix.det_fromBlocks_zero₂₁]
  have hA : A.det = -1 := by
    rw [Matrix.det_fin_one]
  rw [hA]
  ring

#print axioms marked_real_eigenline_block_jacobian
end SpectralRadiusUpperTail
