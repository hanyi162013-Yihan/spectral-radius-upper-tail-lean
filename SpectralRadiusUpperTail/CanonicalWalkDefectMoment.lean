import SpectralRadiusUpperTail.OrientedWalkDefectMoment
import Mathlib.Data.Fintype.Quotient

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

noncomputable def orientedPatternMoment (μ : Measure 𝕂) (s : Fin (2*r) → Bool)
    (R : Setoid (Fin (2*r+1))) [DecidableRel R.r] : 𝕂 :=
  ∫ x : Quotient R × Quotient R → 𝕂,
    (∏ a, if s a then star (x (orientedWalkEdge s (Quotient.mk R) a))
      else x (orientedWalkEdge s (Quotient.mk R) a))
      ∂Measure.pi (fun _ : Quotient R × Quotient R => μ)

/-- Vertex coverage is automatic for the canonical quotient of a path pattern. -/
lemma orientedPatternMoment_vertex_defect_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (s : Fin (2*r) → Bool) (R : Setoid (Fin (2*r+1))) [DecidableRel R.r] :
    ‖orientedPatternMoment μ s R‖ ≤
      (signedWordMomentBase μ c (2*r))^(6*(r+1-Fintype.card (Quotient R))) := by
  apply orientedWalk_vertex_defect_moment_le μ c hc hexp hm hv s (Quotient.mk R)
  intro x
  exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)

#print axioms orientedPatternMoment
#print axioms orientedPatternMoment_vertex_defect_le
end SpectralRadiusUpperTail
