import SpectralRadiusUpperTail.MatrixConditionalWeightedTrace
import SpectralRadiusUpperTail.MatrixGoldenThompson

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Actual conditional trace-exponential step; all exponential and trace
integrability follows from the supplied finite norm bounds. -/
theorem matrix_conditional_trace_exp_step {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {S B : Ω → Matrix ι ι 𝕂} (hS : StronglyMeasurable[m] S)
    (hB : AEStronglyMeasurable B μ)
    (hSh : ∀ᵐ x ∂μ, (S x).IsHermitian) (hBh : ∀ᵐ x ∂μ, (B x).IsHermitian)
    (C D : ℝ) (hSn : ∀ᵐ x ∂μ, ‖S x‖ ≤ C) (hBn : ∀ᵐ x ∂μ, ‖B x‖ ≤ D)
    (hmgf : ∀ᵐ x ∂μ, μ[fun y => NormedSpace.exp (B y) | m] x ≤ 1) :
    Integrable (fun x => RCLike.re (NormedSpace.exp (S x+B x)).trace) μ ∧
      ∀ᵐ x ∂μ, μ[fun y => RCLike.re (NormedSpace.exp (S y+B y)).trace | m] x ≤
        RCLike.re (NormedSpace.exp (S x)).trace := by
  have hec : Continuous (NormedSpace.exp : Matrix ι ι 𝕂 → Matrix ι ι 𝕂) :=
    continuous_iff_continuousAt.mpr fun A =>
      (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt
  have hHe : StronglyMeasurable[m] (fun x => NormedSpace.exp (S x)) :=
    hec.comp_stronglyMeasurable hS
  have hHn : ∀ᵐ x ∂μ, ‖NormedSpace.exp (S x)‖ ≤ Real.exp C := by
    filter_upwards [hSn] with x hx
    exact (algebra_exp_norm_le _).trans (Real.exp_le_exp.mpr hx)
  have hHp : ∀ᵐ x ∂μ, (NormedSpace.exp (S x)).PosSemidef :=
    hSh.mono fun _ hx => matrix_exp_posSemidef hx
  have hiB := algebra_exp_integrable_of_bound hB D hBn
  have hw := matrix_conditional_weighted_trace hm hHe (Real.exp C) hHn hHp hiB hmgf
  have hsum : AEStronglyMeasurable (fun x => S x+B x) μ :=
    (hS.mono hm).aestronglyMeasurable.add hB
  have hsumN : ∀ᵐ x ∂μ, ‖S x+B x‖ ≤ C+D := by
    filter_upwards [hSn,hBn] with x hs hb
    exact (norm_add_le _ _).trans (add_le_add hs hb)
  have hi := algebra_exp_integrable_of_bound hsum (C+D) hsumN
  have hit : Integrable (fun x => RCLike.re (NormedSpace.exp (S x+B x)).trace) μ :=
    (matrixRealTrace : Matrix ι ι 𝕂 →L[ℝ] ℝ).integrable_comp hi
  have hpoint : ∀ᵐ x ∂μ, RCLike.re (NormedSpace.exp (S x+B x)).trace ≤
      RCLike.re (NormedSpace.exp (S x)*NormedSpace.exp (B x)).trace := by
    filter_upwards [hSh,hBh] with x hs hb
    exact matrix_golden_thompson _ _ hs hb
  refine ⟨hit, ?_⟩
  filter_upwards [condExp_mono hit hw.1 hpoint,hw.2] with x h1 h2
  exact h1.trans h2

#print axioms matrix_conditional_trace_exp_step
end SpectralRadiusUpperTail
