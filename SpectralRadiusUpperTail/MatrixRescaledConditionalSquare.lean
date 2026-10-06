import SpectralRadiusUpperTail.MatrixNormTransport
import SpectralRadiusUpperTail.GaussianHermitianVariance

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Rescaling and changing the Banach norm transports the actual conditional square.
The square in the original finite-function space is explicitly matrix multiplication. -/
theorem matrix_rescaled_conditional_square {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (F : Ω → ι → ι → 𝕂) (b : ℝ)
    (hi : Integrable (ε := ι → ι → 𝕂) (fun x => (matrixSelfProduct (F x) : ι → ι → 𝕂)) μ) :
    μ[fun x => (b • matrixL2Equiv (F x))^2 | m] =ᵐ[μ]
      (fun x => b^2 • matrixL2Equiv ((MeasureTheory.condExp (E := ι → ι → 𝕂) m μ (fun y => matrixSelfProduct (F y))) x)) := by
  let T : (ι → ι → 𝕂) →L[ℝ] Matrix ι ι 𝕂 :=
    matrixL2Equiv.toContinuousLinearMap.restrictScalars ℝ
  let L : (ι → ι → 𝕂) →L[ℝ] Matrix ι ι 𝕂 := b^2 • T
  have he : (fun x => (b • matrixL2Equiv (F x))^2) =
      L ∘ (fun x => matrixSelfProduct (F x)) := by
    funext x
    change (b • matrixL2Equiv (F x))^2 = b^2 • matrixL2Equiv (matrixSelfProduct (F x))
    rw [smul_pow]
    congr 1
    change (matrixL2Equiv (F x))^2 = matrixL2Equiv (matrixSelfProduct (F x))
    rw [pow_two]
    rfl
  rw [he]
  exact (L.comp_condExp_comm hi).symm

#print axioms matrix_rescaled_conditional_square
end SpectralRadiusUpperTail
