import SpectralRadiusUpperTail.RealSchurMixedOutputRotation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realMatrixEntryCLM (ι : Type*) [Fintype ι] (i j : ι) :
    Matrix ι ι ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun A := A i j
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- Read a matrix-valued Fréchet derivative along a line through an entry.
The matrix carries the same operator norm as the Schur change of variables. -/
theorem realMatrixEntry_line_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (f : E → Matrix ι ι ℝ) (u h : E) (hf : DifferentiableAt ℝ f u) (i j : ι) :
    HasDerivAt (fun t : ℝ => f (u+t • h) i j) ((fderiv ℝ f u h) i j) 0 := by
  have hline : HasDerivAt (fun t : ℝ => u+t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add u
  have he := (realMatrixEntryCLM ι i j).hasFDerivAt.comp u hf.hasFDerivAt
  have hh := he.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hh

#print axioms realMatrixEntry_line_hasDerivAt
end SpectralRadiusUpperTail
