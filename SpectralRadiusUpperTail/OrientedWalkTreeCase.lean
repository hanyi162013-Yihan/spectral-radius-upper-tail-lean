import SpectralRadiusUpperTail.OrientedWalkNonzeroVertices

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- A nonzero path attaining the vertex ceiling has tree support and every
underlying iid entry occurs exactly twice. -/
lemma orientedWalk_extremal_tree (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0)
    (hcard : Fintype.card ι = r+1) :
    (Finset.univ.image (orientedWalkEdge s v)).card = r ∧
    (∑ e : ι × ι, (entryMultiplicity (orientedWalkEdge s v) e-2)) = 0 ∧
    (walkSupportGraph (Finset.univ.image (orientedWalkEdge s v))).IsTree ∧
    ∀ e ∈ Finset.univ.image (orientedWalkEdge s v), entryMultiplicity (orientedWalkEdge s v) e = 2 := by
  have hlen := iidSignedWord_support_excess μ hm (orientedWalkEdge s v) s hn
  simp only [Fintype.card_fin] at hlen
  have hv := orientedWalk_vertex_card_le s v hcover
  have he : (Finset.univ.image (orientedWalkEdge s v)).card = r := by omega
  have hz : (∑ e : ι × ι, (entryMultiplicity (orientedWalkEdge s v) e-2)) = 0 := by omega
  refine ⟨he,hz,?_,?_⟩
  · apply walkSupportGraph_tree_of_card _ (orientedWalk_support_connected s v hcover)
    omega
  · intro e hem
    have hpos : 0 < entryMultiplicity (orientedWalkEdge s v) e := by
      apply (entryMultiplicity_pos_iff _ _).mpr
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hem
      exact ⟨a,ha⟩
    have hsingle := iidSignedWord_no_singleton μ hm (orientedWalkEdge s v) s hn e
    have hle : entryMultiplicity (orientedWalkEdge s v) e-2 ≤
        ∑ j : ι × ι, (entryMultiplicity (orientedWalkEdge s v) j-2) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (entryMultiplicity (orientedWalkEdge s v) j-2)) (Finset.mem_univ e)
    omega

#print axioms orientedWalk_extremal_tree
end SpectralRadiusUpperTail
