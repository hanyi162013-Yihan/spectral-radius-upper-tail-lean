import SpectralRadiusUpperTail.RealMatrixEntryDifferential

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realMatrixColumnCLM (ι : Type*) [Fintype ι] (j : ι) :
    Matrix ι ι ℝ →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun A := fun i => A i j
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

theorem realMatrixColumn_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (f : E → Matrix ι ι ℝ)
    (u h : E) (hf : DifferentiableAt ℝ f u) (j : ι) :
    fderiv ℝ (fun x => realMatrixColumnCLM ι j (f x)) u h =
      realMatrixColumnCLM ι j (fderiv ℝ f u h) := by
  have hh := (realMatrixColumnCLM ι j).hasFDerivAt.comp u hf.hasFDerivAt
  erw [hh.fderiv]
  rfl

#print axioms realMatrixColumn_fderiv
end SpectralRadiusUpperTail
