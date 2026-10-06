import SpectralRadiusUpperTail.WalkSupportOrientation

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With no loops or opposite orientations, forgetting orientation preserves
the exact edge count. -/
lemma walkSupportGraph_edge_card_of_orientation (E : Finset (V × V))
    (hloop : ∀ a b, (a,b) ∈ E → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ E → (b,a) ∉ E) :
    (walkSupportGraph E).edgeFinset.card = E.card := by
  classical
  have heq : (walkSupportGraph E).edgeFinset = E.image (fun e => s(e.1,e.2)) := by
    apply Finset.Subset.antisymm (walkSupportGraph_edges_subset E)
    intro e he
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp he
    have h : (walkSupportGraph E).Adj a b := ⟨hloop a b hab,Or.inl hab⟩
    simpa using h
  rw [heq]
  apply Finset.card_image_iff.mpr
  intro x hx y hy h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Prod.ext h.1 h.2
  · exfalso
    apply hno x.1 x.2 hx
    have hswap : (x.2,x.1) = y := Prod.ext h.2 h.1
    rwa [hswap]

lemma oriented_tree_vertex_card (E : Finset (V × V))
    (ht : (walkSupportGraph E).IsTree)
    (hloop : ∀ a b, (a,b) ∈ E → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ E → (b,a) ∉ E) :
    Fintype.card V = E.card + 1 := by
  rw [← walkSupportGraph_edge_card_of_orientation E hloop hno]
  exact ht.card_edgeFinset.symm

#print axioms walkSupportGraph_edge_card_of_orientation
#print axioms oriented_tree_vertex_card
end SpectralRadiusUpperTail
