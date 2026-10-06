import SpectralRadiusUpperTail.VisitedWalkCardinality
import SpectralRadiusUpperTail.SegmentRouteMatching

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A primitive route has an actual vertex path with precisely its signed
entry labels. This separates the finite path conversion from its uses. -/
lemma treeRoute_exists_entry_path (p : SegmentRoute V (V × V))
    (hp : OrientedSegmentChain (fun e => e) p.start p.finish p.tokens) :
    ∃ v : Fin (p.tokens.length+1) → V,
      v 0 = p.start ∧ v (Fin.last p.tokens.length) = p.finish ∧
      ∀ i, orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2) v i =
        (p.tokens.get i).1 := by
  obtain ⟨v,hv0,hvl,hv⟩ := hp.exists_fin_path
  refine ⟨v,hv0,hvl,?_⟩
  intro i
  have hs := (hv i).1
  have hf := (hv i).2
  cases hi : (p.tokens.get i).2
  · simp only [segmentTokenStart,segmentTokenFinish,hi,Bool.false_eq_true,if_false] at hs hf
    simp only [orientedWalkEdge,hi,Bool.false_eq_true,if_false]
    exact Prod.ext hs.symm hf.symm
  · simp only [segmentTokenStart,segmentTokenFinish,hi,if_true] at hs hf
    simp only [orientedWalkEdge,hi,if_true]
    exact Prod.ext hf.symm hs.symm

/-- Local vertex data for a route, with ambient unvisited vertices excluded. -/
structure TreeRouteLocalVertices (p : SegmentRoute V (V × V)) where
  vertices : Fin (p.tokens.length+1) → V
  initial : vertices 0 = p.start
  terminal : vertices (Fin.last p.tokens.length) = p.finish
  entries : ∀ i, orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2) vertices i =
    (p.tokens.get i).1
  vertex_card : Nat.card (Set.range vertices) = (p.tokens.map Prod.fst).toFinset.card + 1

lemma treeRoute_local_vertices (T : Finset (V × V)) (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (p : SegmentRoute V (V × V))
    (hp : OrientedSegmentChain (fun e => e) p.start p.finish p.tokens)
    (hT : ∀ t ∈ p.tokens, t.1 ∈ T) : Nonempty (TreeRouteLocalVertices p) := by
  classical
  obtain ⟨v,hv0,hvl,hv⟩ := treeRoute_exists_entry_path p hp
  let s : Fin p.tokens.length → Bool := fun j => (p.tokens.get j).2
  have he : Finset.univ.image (orientedWalkEdge s v) = (p.tokens.map Prod.fst).toFinset := by
    ext e
    constructor
    · intro h
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      rw [hv]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p.tokens.get i,List.get_mem p.tokens i,rfl⟩)
    · intro h
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      obtain ⟨i,hi⟩ := List.get_of_mem ht
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,(hv i).trans (congrArg Prod.fst hi)⟩
  have hsub : Finset.univ.image (orientedWalkEdge s v) ⊆ T := by
    intro e he'
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he'
    rw [hv]
    exact hT _ (List.get_mem p.tokens i)
  have hc := visitedWalk_card_eq_entries_add_one T ht hloop hno s v hsub
  rw [he] at hc
  exact ⟨⟨v,hv0,hvl,hv,hc⟩⟩

#print axioms treeRoute_exists_entry_path
#print axioms TreeRouteLocalVertices
#print axioms treeRoute_local_vertices
end SpectralRadiusUpperTail
