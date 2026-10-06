import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Data.Matrix.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

/-- Insert one scalar into its original matrix coordinate. This is a real
continuous linear map, so it preserves conditional centering in both fields. -/
noncomputable def matrixCoordinateL (i j : Fin N) : 𝕂 →L[ℝ] Matrix (Fin N) (Fin N) 𝕂 :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.pi fun q =>
    if p=i ∧ q=j then ContinuousLinearMap.id ℝ 𝕂 else 0

lemma matrixCoordinateL_apply (i j p q : Fin N) (z : 𝕂) :
    matrixCoordinateL i j z p q = if p=i ∧ q=j then z else 0 := by
  change (if p=i ∧ q=j then ContinuousLinearMap.id ℝ 𝕂 else 0) z = _
  split_ifs <;> rfl

lemma matrixCoordinateL_descending (n : Fin N) : n.rev.val = N-(n.val+1) := by
  rw [Fin.val_rev]

/-- Any deterministic continuous linear embedding carries actual martingale
differences to actual martingale differences on the same filtered space. -/
theorem condExp_continuousLinear_zero {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → E) (hf : Integrable f P)
    (hz : P[f | m] =ᵐ[P] 0) (L : E →L[ℝ] F) : P[L ∘ f | m] =ᵐ[P] 0 := by
  apply (L.comp_condExp_comm hf).symm.trans
  filter_upwards [hz] with x hx
  simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrArg L hx

#print axioms matrixCoordinateL_apply
#print axioms condExp_continuousLinear_zero
end SpectralRadiusUpperTail
