import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

namespace SpectralRadiusUpperTail
open MeasureTheory Matrix
open scoped MeasureTheory ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι]

/-- The positive semidefinite cone is closed in the finite-function
topology used by the actual matrix-valued conditional expectations. -/
lemma matrix_posSemidef_isClosed :
    IsClosed {A : ι → ι → 𝕂 | Matrix.PosSemidef A} := by
  change IsClosed {A : Matrix ι ι 𝕂 | A.PosSemidef}
  simp_rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

lemma matrix_posSemidef_convex :
    Convex ℝ {A : ι → ι → 𝕂 | Matrix.PosSemidef A} := by
  intro A hA B hB a b ha hb hab
  exact (hA.smul ha).add (hB.smul hb)

/-- A single a.e. set supports positivity in every vector direction.
The proof uses the closed convex cone, avoiding an uncountable
intersection of direction-dependent null sets. -/
theorem matrix_condExp_posSemidef {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {F : Ω → ι → ι → 𝕂} (hF : Integrable F μ)
    (hpos : ∀ᵐ x ∂μ, Matrix.PosSemidef (F x)) :
    ∀ᵐ x ∂μ, Matrix.PosSemidef (μ[F | m] x) := by
  exact matrix_posSemidef_convex.condExp_mem hm hF matrix_posSemidef_isClosed hpos

/-- Conditional expectation preserves the semidefinite order, with
integrability stated in precisely the original finite-function space. -/
theorem matrix_condExp_mono {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {F G : Ω → ι → ι → 𝕂} (hF : Integrable F μ) (hG : Integrable G μ)
    (hFG : ∀ᵐ x ∂μ, Matrix.PosSemidef (G x - F x)) :
    ∀ᵐ x ∂μ, Matrix.PosSemidef (μ[G | m] x - μ[F | m] x) := by
  filter_upwards [matrix_condExp_posSemidef hm (hG.sub hF) hFG,
    condExp_sub hG hF (m := m)] with x hpos heq
  simpa only [heq, Pi.sub_apply] using hpos

#print axioms matrix_condExp_posSemidef
#print axioms matrix_condExp_mono
end SpectralRadiusUpperTail
