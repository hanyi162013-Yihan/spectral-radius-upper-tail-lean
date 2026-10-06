import SpectralRadiusUpperTail.OrientedWalkDefectPruning

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- The deletion bound applies to any chosen support subset with V-1 entries,
so it can be attached to a previously constructed route certificate. -/
lemma orientedWalk_chosen_tree_pruning_budget (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0)
    (T : Finset (ι × ι)) (hT : T ⊆ Finset.univ.image (orientedWalkEdge s v))
    (hcard : T.card+1 = Fintype.card ι) :
    (Finset.univ.filter (fun i => entryMultiplicity (orientedWalkEdge s v)
      (orientedWalkEdge s v i) ≠ 2 ∨ orientedWalkEdge s v i ∉ T)).card ≤
        8*(r+1-Fintype.card ι) := by
  have hno := iidSignedWord_no_singleton μ hm (orientedWalkEdge s v) s hn
  have hD := entryPruning_card_le (orientedWalkEdge s v) T hT hno
  have hlen := iidSignedWord_support_excess μ hm (orientedWalkEdge s v) s hn
  simp only [Fintype.card_fin] at hlen
  have hv := orientedWalk_vertex_card_le s v hcover
  have hV : 1 ≤ Fintype.card ι := by omega
  have hTcard : T.card = Fintype.card ι - 1 := by omega
  rw [hTcard] at hD
  exact entryPruning_defect_budget r _ _ _ _ hlen hv hV hD

#print axioms orientedWalk_chosen_tree_pruning_budget
end SpectralRadiusUpperTail
