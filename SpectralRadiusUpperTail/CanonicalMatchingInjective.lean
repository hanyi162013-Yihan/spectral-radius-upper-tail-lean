import SpectralRadiusUpperTail.MatchingVertexReconstruction
import SpectralRadiusUpperTail.OrientedWalkTreeCase
import SpectralRadiusUpperTail.FiniteEqualityPatterns

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- Two actual nonzero extremal canonical patterns with the same entry matching
are equal as setoids, not merely isomorphic after choosing vertex labels. -/
lemma orientedPattern_eq_of_same_matching (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool)
    (R S : Setoid (Fin (2*r+1))) [DecidableRel R.r] [DecidableRel S.r]
    (hnR : orientedPatternMoment μ s R ≠ 0) (hnS : orientedPatternMoment μ s S ≠ 0)
    (hcR : Fintype.card (Quotient R) = r+1) (hcS : Fintype.card (Quotient S) = r+1)
    (f : Fin (2*r) → Fin (2*r)) (hfix : ∀ i, f i ≠ i)
    (hfR : ∀ i, orientedWalkEdge s (Quotient.mk R) (f i) = orientedWalkEdge s (Quotient.mk R) i)
    (hfS : ∀ i, orientedWalkEdge s (Quotient.mk S) (f i) = orientedWalkEdge s (Quotient.mk S) i) :
    R = S := by
  have hvR : Function.Surjective (Quotient.mk R) := by
    intro x
    exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)
  have hvS : Function.Surjective (Quotient.mk S) := by
    intro x
    exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)
  have htR := orientedWalk_extremal_tree μ hm s (Quotient.mk R) hvR hnR hcR
  have htS := orientedWalk_extremal_tree μ hm s (Quotient.mk S) hvS hnS hcS
  have hoR := walkSupportGraph_oriented_tree _ (orientedWalk_support_connected s (Quotient.mk R) hvR)
    (by rw [htR.1,hcR])
  have hoS := walkSupportGraph_oriented_tree _ (orientedWalk_support_connected s (Quotient.mk S) hvS)
    (by rw [htS.1,hcS])
  have hdR : ∀ i, entryMultiplicity (orientedWalkEdge s (Quotient.mk R))
      (orientedWalkEdge s (Quotient.mk R) i) = 2 := by
    intro i
    exact htR.2.2.2 _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hdS : ∀ i, entryMultiplicity (orientedWalkEdge s (Quotient.mk S))
      (orientedWalkEdge s (Quotient.mk S) i) = 2 := by
    intro i
    exact htS.2.2.2 _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  apply Setoid.ext
  intro a b
  have hv := orientedTree_vertex_pattern_of_matching s s (Quotient.mk R) (Quotient.mk S)
    hoR.1 hoS.1 hoR.2.1 hoS.2.1 hoR.2.2 hoS.2.2 hdR hdS f hfix hfR hfS a b
  exact Quotient.eq.symm.trans (hv.trans Quotient.eq)

#print axioms orientedPattern_eq_of_same_matching
end SpectralRadiusUpperTail
