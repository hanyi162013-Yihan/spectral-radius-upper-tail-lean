import SpectralRadiusUpperTail.CanonicalWalkDefectMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

lemma orientedWalk_nonzero_vertex_bound (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    Fintype.card ι ≤ r+1 := by
  have hlen := iidSignedWord_support_excess μ hm (orientedWalkEdge s v) s hn
  simp only [Fintype.card_fin] at hlen
  have hv := orientedWalk_vertex_card_le s v hcover
  omega

lemma orientedPatternMoment_nonzero_vertices (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool)
    (R : Setoid (Fin (2*r+1))) [DecidableRel R.r]
    (hn : orientedPatternMoment μ s R ≠ 0) : Fintype.card (Quotient R) ≤ r+1 := by
  apply orientedWalk_nonzero_vertex_bound μ hm s (Quotient.mk R) _ hn
  intro x
  exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)

#print axioms orientedWalk_nonzero_vertex_bound
#print axioms orientedPatternMoment_nonzero_vertices
end SpectralRadiusUpperTail
