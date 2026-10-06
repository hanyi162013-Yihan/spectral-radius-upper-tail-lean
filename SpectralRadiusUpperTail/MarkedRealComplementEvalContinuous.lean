import SpectralRadiusUpperTail.MarkedRealTwoBlockRootBranch
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The complementary characteristic polynomial evaluated at a real
parameter varies continuously with the matrix and parameter. -/
theorem continuous_markedRealComplement_charpoly_eval (m : ℕ) :
    Continuous (fun p :
      Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ × ℝ =>
      (markedRealComplement m p.1).charpoly.eval p.2) := by
  have hmat : Continuous (fun p :
      Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ × ℝ =>
        Matrix.scalar (Fin m) p.2 - markedRealComplement m p.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simp only [Matrix.sub_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply, if_pos hij]
      fun_prop
    · simp only [Matrix.sub_apply, Matrix.scalar_apply,
        Matrix.diagonal_apply, if_neg hij]
      fun_prop
  have h := hmat.matrix_det
  convert h using 1
  funext p
  exact Matrix.eval_charpoly (markedRealComplement m p.1) p.2

#print axioms continuous_markedRealComplement_charpoly_eval
end SpectralRadiusUpperTail
