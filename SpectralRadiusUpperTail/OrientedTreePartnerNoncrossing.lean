import SpectralRadiusUpperTail.OrientedEdgeSymmetry
import SpectralRadiusUpperTail.DoubleWordPartnerFiber
import SpectralRadiusUpperTail.FiniteBridgeNoninterleaving

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The actual repeated-entry partner map of an oriented tree path is noncrossing.
The absence of extra geometric occurrences is derived from multiplicity two. -/
lemma orientedTree_partner_noncrossing (s : Fin n → Bool) (p : Fin (n+1) → ι)
    (ht : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).IsTree)
    (hloop : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge s p))
    (hm : ∀ i, entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) = 2)
    (i k : Fin n) (hik : i < k)
    (hkj : k < doubleWordPartner (orientedWalkEdge s p) hm i)
    (hjl : doubleWordPartner (orientedWalkEdge s p) hm i <
      doubleWordPartner (orientedWalkEdge s p) hm k) : False := by
  let G := walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))
  let f := doubleWordPartner (orientedWalkEdge s p) hm
  have hadj (t : Fin n) : G.Adj (p t.castSucc) (p t.succ) :=
    orientedWalk_step_adj s p hloop t
  have hb : G.IsBridge s(p i.castSucc,p i.succ) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic (hadj i)
  apply finiteBridgePath_no_interleaving G (p i.castSucc) (p i.succ) hb p i k (f i) (f k)
    hik hkj hjl hadj
  · exact (orientedWalkEdge_eq_iff_geometric s p hno (f i) i).mp
      (doubleWordPartner_spec (orientedWalkEdge s p) hm i).2
  · intro t hit htl htj he
    have hentry := (orientedWalkEdge_eq_iff_geometric s p hno t i).mpr he
    rcases (doubleWord_entry_eq_iff (orientedWalkEdge s p) hm i t).mp hentry with h | h
    · exact (ne_of_gt hit) h
    · exact htj h
  · exact (orientedWalkEdge_eq_iff_geometric s p hno k (f k)).mp
      (doubleWordPartner_spec (orientedWalkEdge s p) hm k).2.symm

#print axioms orientedTree_partner_noncrossing
end SpectralRadiusUpperTail
