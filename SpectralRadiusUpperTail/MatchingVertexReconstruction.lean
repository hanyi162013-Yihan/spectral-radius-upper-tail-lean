import SpectralRadiusUpperTail.OrientedTreePatternReconstruction
import SpectralRadiusUpperTail.MatchingEntryPattern

namespace SpectralRadiusUpperTail
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] {n : ℕ}

/-- The same fixed-point-free entry matching on two double-tree paths
forces their full vertex equality patterns to agree. -/
lemma orientedTree_vertex_pattern_of_matching
    (s t : Fin n → Bool) (p : Fin (n+1) → V) (q : Fin (n+1) → W)
    (hp : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).IsTree)
    (hq : (walkSupportGraph (Finset.univ.image (orientedWalkEdge t q))).IsTree)
    (hpl : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → a ≠ b)
    (hql : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge t q) → a ≠ b)
    (hpn : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge s p))
    (hqn : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge t q) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge t q))
    (hmp : ∀ i, entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) = 2)
    (hmq : ∀ i, entryMultiplicity (orientedWalkEdge t q) (orientedWalkEdge t q i) = 2)
    (f : Fin n → Fin n) (hfix : ∀ i, f i ≠ i)
    (hfp : ∀ i, orientedWalkEdge s p (f i) = orientedWalkEdge s p i)
    (hfq : ∀ i, orientedWalkEdge t q (f i) = orientedWalkEdge t q i)
    (a b : Fin (n+1)) : p a = p b ↔ q a = q b := by
  apply orientedTree_vertex_pattern_of_edge_pattern s t p q hp hq hpl hql hpn hqn _ a b
  intro i j
  exact (doubleWord_entry_eq_iff_matching (orientedWalkEdge s p) hmp f hfix hfp j i).trans
    (doubleWord_entry_eq_iff_matching (orientedWalkEdge t q) hmq f hfix hfq j i).symm

#print axioms orientedTree_vertex_pattern_of_matching
end SpectralRadiusUpperTail
