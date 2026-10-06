import SpectralRadiusUpperTail.TreeCutBothOrientations
import SpectralRadiusUpperTail.OrientedEdgeSymmetry

namespace SpectralRadiusUpperTail
variable {V : Type*}

lemma tree_cut_signature_injective {n : ℕ} (G : SimpleGraph V) (ht : G.IsTree)
    (p : Fin (n+1) → V)
    (hcover : ∀ a b, G.Adj a b → ∃ i : Fin n, s(p i.castSucc,p i.succ) = s(a,b))
    (x y : V)
    (he : ∀ i : Fin n, bridgeCutColor G (p i.castSucc) (p i.succ) x =
      bridgeCutColor G (p i.castSucc) (p i.succ) y) : x = y := by
  by_contra hxy
  obtain ⟨z,hz,hforward,hreverse⟩ := tree_bridgeCut_separates_both G ht x y hxy
  obtain ⟨i,hi⟩ := hcover x z hz
  have hc := he i
  rcases Sym2.eq_iff.mp hi with h | h
  · rw [h.1,h.2] at hc
    exact hforward hc
  · rw [h.1,h.2] at hc
    exact hreverse hc

variable [Fintype V] [DecidableEq V]

lemma orientedWalk_support_edge_cover {n : ℕ} (s : Fin n → Bool) (p : Fin (n+1) → V)
    (a b : V) (h : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).Adj a b) :
    ∃ i : Fin n, s(p i.castSucc,p i.succ) = s(a,b) := by
  rcases h.2 with hab | hba
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hab
    refine ⟨i,?_⟩
    rw [← orientedWalkEdge_sym2 s p i,hi]
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hba
    refine ⟨i,?_⟩
    rw [← orientedWalkEdge_sym2 s p i,hi]
    exact Sym2.eq_swap

/-- In an actual oriented tree support, all vertex equalities are detected by
cut colors indexed by the path's edge positions. -/
lemma orientedTree_vertex_eq_iff_cuts {n : ℕ} (s : Fin n → Bool) (p : Fin (n+1) → V)
    (ht : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).IsTree)
    (a b : Fin (n+1)) :
    p a = p b ↔ ∀ i : Fin n,
      bridgeCutColor (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p)))
        (p i.castSucc) (p i.succ) (p a) =
      bridgeCutColor (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p)))
        (p i.castSucc) (p i.succ) (p b) := by
  constructor
  · intro h i
    rw [h]
  · intro h
    exact tree_cut_signature_injective _ ht p (orientedWalk_support_edge_cover s p) _ _ h

#print axioms tree_cut_signature_injective
#print axioms orientedWalk_support_edge_cover
#print axioms orientedTree_vertex_eq_iff_cuts
end SpectralRadiusUpperTail
