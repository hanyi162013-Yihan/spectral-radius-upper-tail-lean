import SpectralRadiusUpperTail.DirectedSpanningTree
import SpectralRadiusUpperTail.EntryPruningMass
import SpectralRadiusUpperTail.OrientedWalkDefectMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

/-- Every actual nonzero covered word can be pruned by at most eight positions
per vertex defect so that all surviving entries are double edges in a fixed
oriented spanning tree. No assertion about counting the original patterns is
made here: segment reordering and an injective reconstruction are still needed. -/
lemma orientedWalk_exists_defect_pruning (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    ∃ (T : Finset (ι × ι)) (D : Finset (Fin (2*r))),
      T ⊆ Finset.univ.image (orientedWalkEdge s v) ∧
      (walkSupportGraph T).IsTree ∧ T.card + 1 = Fintype.card ι ∧
      (∀ a b, (a,b) ∈ T → a ≠ b) ∧
      (∀ a b, (a,b) ∈ T → (b,a) ∉ T) ∧
      D.card ≤ 8*(r+1-Fintype.card ι) ∧
      (∀ a, a ∉ D ↔ orientedWalkEdge s v a ∈ T ∧
        entryMultiplicity (orientedWalkEdge s v) (orientedWalkEdge s v a) = 2) := by
  classical
  let e := orientedWalkEdge s v
  obtain ⟨T,hT,htree,hcard,hloop,hop⟩ := directedSupport_exists_spanning_tree
    (Finset.univ.image e) (orientedWalk_support_connected s v hcover)
  let D := Finset.univ.filter (fun a => entryMultiplicity e (e a) ≠ 2 ∨ e a ∉ T)
  refine ⟨T,D,hT,htree,hcard,hloop,hop,?_,?_⟩
  · have hno := iidSignedWord_no_singleton μ hm e s hn
    have hD := entryPruning_card_le e T hT hno
    have hlen := iidSignedWord_support_excess μ hm e s hn
    simp only [Fintype.card_fin] at hlen
    have hv := orientedWalk_vertex_card_le s v hcover
    have hV : 1 ≤ Fintype.card ι := by omega
    have hTcard : T.card = Fintype.card ι - 1 := by omega
    rw [hTcard] at hD
    exact entryPruning_defect_budget r _ _ _ _ hlen hv hV hD
  · intro a
    simp only [D,Finset.mem_filter,Finset.mem_univ,true_and,not_or,not_not]
    exact and_comm

#print axioms orientedWalk_exists_defect_pruning
end SpectralRadiusUpperTail
