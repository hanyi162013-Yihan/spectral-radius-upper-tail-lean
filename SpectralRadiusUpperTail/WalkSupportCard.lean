import SpectralRadiusUpperTail.WalkSupportGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

instance walkSupportGraph_decidable (E : Finset (ι × ι)) :
    DecidableRel (walkSupportGraph E).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun a b => (a,b) ∈ E)).Adj)

lemma walkSupportGraph_edges_subset (E : Finset (ι × ι)) :
    (walkSupportGraph E).edgeFinset ⊆ E.image (fun e => s(e.1,e.2)) := by
  intro edge
  refine Sym2.inductionOn edge (fun a b he => ?_)
  have h : (walkSupportGraph E).Adj a b := by simpa using he
  rcases h.2 with hab | hba
  · exact Finset.mem_image.mpr ⟨(a,b),hab,rfl⟩
  · exact Finset.mem_image.mpr ⟨(b,a),hba,Sym2.eq_swap⟩

lemma walkSupportGraph_edge_card_le (E : Finset (ι × ι)) :
    (walkSupportGraph E).edgeFinset.card ≤ E.card :=
  le_trans (Finset.card_le_card (walkSupportGraph_edges_subset E)) (Finset.card_image_le)

/-- Connected directed support has at most one more vertex than directed edges. -/
lemma walkSupportGraph_vertex_card_le (E : Finset (ι × ι))
    (h : (walkSupportGraph E).Connected) : Fintype.card ι ≤ E.card+1 := by
  have hv := h.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at hv
  have he := walkSupportGraph_edge_card_le E
  omega

/-- Equality in the directed edge bound forces the undirected support to be a tree. -/
lemma walkSupportGraph_tree_of_card (E : Finset (ι × ι))
    (h : (walkSupportGraph E).Connected) (hc : E.card+1 = Fintype.card ι) :
    (walkSupportGraph E).IsTree := by
  have hv := h.card_vert_le_card_edgeSet_add_one
  have he := walkSupportGraph_edge_card_le E
  have hh : Nat.card (walkSupportGraph E).edgeSet+1 = Nat.card ι := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← SimpleGraph.edgeFinset_card] at hv ⊢
    omega
  exact (SimpleGraph.isTree_iff_connected_and_card).mpr ⟨h,hh⟩

#print axioms walkSupportGraph_decidable
#print axioms walkSupportGraph_edges_subset
#print axioms walkSupportGraph_edge_card_le
#print axioms walkSupportGraph_vertex_card_le
#print axioms walkSupportGraph_tree_of_card
end SpectralRadiusUpperTail
