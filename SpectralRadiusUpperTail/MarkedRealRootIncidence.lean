import SpectralRadiusUpperTail.MarkedRealFixedRootRegularFrame
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Matrix–real-root pairs form the marked spectral incidence set. -/
def markedRealRootIncidence (n : ℕ) :
    Set (Matrix (Fin n) (Fin n) ℝ × ℝ) :=
  {p | p.1.charpoly.eval p.2 = 0}

theorem markedRealRootIncidence_isClosed (n : ℕ) :
    IsClosed (markedRealRootIncidence n) := by
  have hmat : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      Matrix.scalar (Fin n) p.2 - p.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        if_pos hij]
      fun_prop
    · simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        if_neg hij]
      fun_prop
  have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ℝ =>
      p.1.charpoly.eval p.2) := by
    have h := hmat.matrix_det
    convert h using 1
    funext p
    exact Matrix.eval_charpoly p.1 p.2
  change IsClosed ((fun p : Matrix (Fin n) (Fin n) ℝ × ℝ =>
    p.1.charpoly.eval p.2) ⁻¹' {0})
  exact isClosed_singleton.preimage hcont

theorem markedRealRootIncidence_finite_fiber (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Set.Finite {x : ℝ | (A,x) ∈ markedRealRootIncidence n} := by
  have hp : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  exact Polynomial.finite_setOfPred_isRoot hp

#print axioms markedRealRootIncidence_isClosed
#print axioms markedRealRootIncidence_finite_fiber
end SpectralRadiusUpperTail
