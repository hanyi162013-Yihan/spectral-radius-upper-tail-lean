import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace SpectralRadiusUpperTail

theorem scalar_vector_cone_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x h : ℝ × E) (hf : DifferentiableAt ℝ f x.2) :
    fderiv ℝ (fun y : ℝ × E => y.1 • f y.2) x h =
      x.1 • fderiv ℝ f x.2 h.2 + h.1 • f x.2 := by
  have hg := hf.hasFDerivAt.comp x hasFDerivAt_snd
  have hr : HasFDerivAt (fun y : ℝ × E => y.1)
      (ContinuousLinearMap.fst ℝ ℝ E) x := hasFDerivAt_fst
  have hh := hr.smul hg
  erw [hh.fderiv]
  rfl

#print axioms scalar_vector_cone_fderiv
end SpectralRadiusUpperTail
