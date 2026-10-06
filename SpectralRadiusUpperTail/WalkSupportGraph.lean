import SpectralRadiusUpperTail.ListWalkCount
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι]

/-- The undirected support of a finite set of directed entries; loops are
 discarded, and opposite orientations share one undirected edge. -/
def walkSupportGraph (E : Finset (ι × ι)) : SimpleGraph ι :=
  SimpleGraph.fromRel (fun a b => (a,b) ∈ E)

lemma walkSupportGraph_edge_reachable (E : Finset (ι × ι)) {a b : ι}
    (h : (a,b) ∈ E) : (walkSupportGraph E).Reachable a b := by
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.refl _
  · exact (show (walkSupportGraph E).Adj a b from ⟨hab,Or.inl h⟩).reachable

lemma listWalk_head_reachable (E : Finset (ι × ι)) (a : ι) (l : List ι)
    (hE : listWalkEdges (a :: l) ⊆ E) :
    ∀ x ∈ a :: l, (walkSupportGraph E).Reachable a x := by
  induction l generalizing a with
  | nil =>
    intro x hx
    have hx : x = a := by simpa using hx
    subst x
    exact SimpleGraph.Reachable.refl _
  | cons b rest ih =>
    have ht : listWalkEdges (b :: rest) ⊆ E :=
      fun _ he => hE (Finset.mem_insert_of_mem he)
    have hab := walkSupportGraph_edge_reachable E
      (hE (Finset.mem_insert_self (a,b) (listWalkEdges (b :: rest))))
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      exact SimpleGraph.Reachable.refl _
    · exact hab.trans (ih b ht x hx)

lemma listWalk_vertices_reachable (E : Finset (ι × ι)) (l : List ι)
    (hE : listWalkEdges l ⊆ E) {a b : ι} (ha : a ∈ l) (hb : b ∈ l) :
    (walkSupportGraph E).Reachable a b := by
  cases l with
  | nil => simp at ha
  | cons c rest =>
    exact (listWalk_head_reachable E c rest hE a ha).symm.trans
      (listWalk_head_reachable E c rest hE b hb)

/-- Two vertex lists covering the vertex type and sharing a directed edge
 have a connected undirected support. -/
lemma pairedWalk_support_connected (l r : List ι) (edge : ι × ι)
    (hl : edge ∈ listWalkEdges l) (hr : edge ∈ listWalkEdges r)
    (hcover : ∀ x, x ∈ l ∨ x ∈ r) :
    (walkSupportGraph (listWalkEdges l ∪ listWalkEdges r)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨edge.1, fun x => ?_⟩
  rcases hcover x with hx | hx
  · exact listWalk_vertices_reachable _ l Finset.subset_union_left
      (listWalkEdges_endpoints hl).1 hx
  · exact listWalk_vertices_reachable _ r Finset.subset_union_right
      (listWalkEdges_endpoints hr).1 hx

#print axioms walkSupportGraph_edge_reachable
#print axioms listWalk_head_reachable
#print axioms listWalk_vertices_reachable
#print axioms pairedWalk_support_connected
end SpectralRadiusUpperTail
