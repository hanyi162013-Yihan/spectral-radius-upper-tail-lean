import SpectralRadiusUpperTail.MatrixConditionalOrder
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restrict the operator-norm algebra to real scalars, including proper
complex entries. Registered only locally by the modules using it. -/
@[instance_reducible]
noncomputable def matrixL2RealNormedAlgebra : NormedAlgebra ℝ (Matrix ι ι 𝕂) where
  norm_smul_le r B := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕂)]
    simpa using (norm_smul_le (r : 𝕂) B)

attribute [local instance] matrixL2RealNormedAlgebra

/-- Identity on matrix entries, with the finite-function norm on the
source and the Euclidean operator norm on the target. Continuity in
both directions is proved by finite dimensionality over the entry field. -/
noncomputable def matrixL2Equiv : (ι → ι → 𝕂) ≃L[𝕂] Matrix ι ι 𝕂 :=
  (show (ι → ι → 𝕂) ≃ₗ[𝕂] Matrix ι ι 𝕂 from LinearEquiv.refl 𝕂 _).toContinuousLinearEquiv

lemma matrixL2Equiv_apply (A : ι → ι → 𝕂) : matrixL2Equiv A = A := rfl

lemma matrixL2Equiv_symm_apply (A : Matrix ι ι 𝕂) : matrixL2Equiv.symm A = A := rfl

/-- This equality explicitly connects conditional expectations taken
in the two Banach-space structures; it is not a change of norm instance
inside an already constructed conditional expectation. -/
theorem matrixL2_condExp {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {F : Ω → ι → ι → 𝕂} (hF : Integrable F μ) :
    (fun x => matrixL2Equiv (μ[F | m] x)) =ᵐ[μ]
      μ[matrixL2Equiv ∘ F | m] := by
  let L : (ι → ι → 𝕂) →L[ℝ] Matrix ι ι 𝕂 :=
    matrixL2Equiv.toContinuousLinearMap.restrictScalars ℝ
  exact L.comp_condExp_comm hF

theorem matrixL2_condExp_posSemidef {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {F : Ω → Matrix ι ι 𝕂} (hF : Integrable F μ)
    (hpos : ∀ᵐ x ∂μ, (F x).PosSemidef) :
    ∀ᵐ x ∂μ, (μ[F | m] x).PosSemidef := by
  let L : Matrix ι ι 𝕂 →L[ℝ] (ι → ι → 𝕂) :=
    matrixL2Equiv.symm.toContinuousLinearMap.restrictScalars ℝ
  have hi : Integrable (L ∘ F) μ := L.integrable_comp hF
  have hp : ∀ᵐ x ∂μ, Matrix.PosSemidef ((L ∘ F) x) := hpos
  filter_upwards [matrix_condExp_posSemidef hm hi hp, L.comp_condExp_comm hF (m := m)]
    with x hx heq
  change Matrix.PosSemidef (L (μ[F | m] x))
  exact (congrArg (fun B : ι → ι → 𝕂 => Matrix.PosSemidef B) heq).mpr hx

#print axioms matrixL2_condExp
#print axioms matrixL2_condExp_posSemidef
end SpectralRadiusUpperTail
