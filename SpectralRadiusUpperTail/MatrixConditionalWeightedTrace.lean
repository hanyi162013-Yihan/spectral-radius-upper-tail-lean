import SpectralRadiusUpperTail.MatrixWeightedTrace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

noncomputable def matrixRealTrace : Matrix ι ι 𝕂 →L[ℝ] ℝ :=
  RCLike.reCLM.comp ((Matrix.traceLinearMap ι 𝕂 𝕂).toContinuousLinearMap.restrictScalars ℝ)

lemma matrixRealTrace_apply (A : Matrix ι ι 𝕂) : matrixRealTrace A = RCLike.re A.trace := rfl

/-- Conditional trace bound with the actual bounded predictable PSD weight.
Product and scalar trace integrability are derived, not assumed. -/
theorem matrix_conditional_weighted_trace {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {H Y : Ω → Matrix ι ι 𝕂} (hH : StronglyMeasurable[m] H)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖H x‖ ≤ C)
    (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef) (hY : Integrable Y μ)
    (hce : ∀ᵐ x ∂μ, μ[Y | m] x ≤ 1) :
    Integrable (fun x => RCLike.re (H x*Y x).trace) μ ∧
      ∀ᵐ x ∂μ, μ[fun y => RCLike.re (H y*Y y).trace | m] x ≤ RCLike.re (H x).trace := by
  let B : Matrix ι ι 𝕂 →L[ℝ] Matrix ι ι 𝕂 →L[ℝ] Matrix ι ι 𝕂 :=
    ContinuousLinearMap.mul ℝ _
  let T : Matrix ι ι 𝕂 →L[ℝ] ℝ := matrixRealTrace
  have hi : Integrable (fun x => H x*Y x) μ :=
    B.integrable_of_bilin_of_bdd_left C (hH.mono hm).aestronglyMeasurable hbound hY
  have hit : Integrable (fun x => RCLike.re (H x*Y x).trace) μ := T.integrable_comp hi
  refine ⟨hit, ?_⟩
  filter_upwards [condExp_bilin_of_stronglyMeasurable_left B hH hi hY,
    T.comp_condExp_comm hi (m := m),hpos,hce] with x hp ht hpx hcx
  have he : μ[fun y => H y*Y y | m] x = H x*μ[Y | m] x := by
    simpa only [B,ContinuousLinearMap.mul_apply'] using hp
  calc
    _ = T (μ[fun y => H y*Y y | m] x) := ht.symm
    _ = T (H x*μ[Y | m] x) := congrArg T he
    _ ≤ _ := by
      simpa only [T,matrixRealTrace_apply,Matrix.mul_one] using matrix_weighted_trace_mono hpx hcx

#print axioms matrix_conditional_weighted_trace
end SpectralRadiusUpperTail
