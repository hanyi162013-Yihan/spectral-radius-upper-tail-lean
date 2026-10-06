import SpectralRadiusUpperTail.OrientedTreePartnerNoncrossing
import SpectralRadiusUpperTail.OrientedWalkTreeCase
import SpectralRadiusUpperTail.BlockMatchingCode

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- An actual nonzero path at maximal vertex count supplies a noncrossing
perfect matching of equal iid entries. Sign compatibility and reconstruction
are separate subsequent conclusions. -/
lemma orientedWalk_extremal_matching (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0)
    (hcard : Fintype.card ι = r+1) :
    ∃ f : NoncrossingMatching (2*r), ∀ i,
      orientedWalkEdge s v (f.val i) = orientedWalkEdge s v i := by
  have ht := orientedWalk_extremal_tree μ hm s v hcover hn hcard
  have hor := walkSupportGraph_oriented_tree (Finset.univ.image (orientedWalkEdge s v))
    (orientedWalk_support_connected s v hcover) (by rw [ht.1,hcard])
  have hd : ∀ i, entryMultiplicity (orientedWalkEdge s v) (orientedWalkEdge s v i) = 2 := by
    intro i
    exact ht.2.2.2 _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  let f := doubleWordPartner (orientedWalkEdge s v) hd
  have hnc : ∀ i k, i < k → k < f i → f i < f k → False :=
    orientedTree_partner_noncrossing s v hor.1 hor.2.1 hor.2.2 hd
  refine ⟨⟨f, doubleWordPartner_involutive _ hd,
    (fun i => (doubleWordPartner_spec _ hd i).1), hnc⟩,?_⟩
  intro i
  exact (doubleWordPartner_spec _ hd i).2

#print axioms orientedWalk_extremal_matching
end SpectralRadiusUpperTail
