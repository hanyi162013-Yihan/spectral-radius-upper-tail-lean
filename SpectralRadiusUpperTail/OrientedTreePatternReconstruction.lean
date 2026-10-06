import SpectralRadiusUpperTail.TreePathCutSignature
import SpectralRadiusUpperTail.BoolPathEquality
import SpectralRadiusUpperTail.BridgeCutStep

namespace SpectralRadiusUpperTail
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] {n : ℕ}

/-- For oriented tree supports, equality of edge-occurrence patterns determines
all vertex equalities. The two paths may use different vertex types. -/
lemma orientedTree_vertex_pattern_of_edge_pattern
    (s t : Fin n → Bool) (p : Fin (n+1) → V) (q : Fin (n+1) → W)
    (hp : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).IsTree)
    (hq : (walkSupportGraph (Finset.univ.image (orientedWalkEdge t q))).IsTree)
    (hpl : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → a ≠ b)
    (hql : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge t q) → a ≠ b)
    (hpn : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge s p))
    (hqn : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge t q) →
      (b,a) ∉ Finset.univ.image (orientedWalkEdge t q))
    (he : ∀ i j, orientedWalkEdge s p i = orientedWalkEdge s p j ↔
      orientedWalkEdge t q i = orientedWalkEdge t q j)
    (a b : Fin (n+1)) : p a = p b ↔ q a = q b := by
  let G := walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))
  let H := walkSupportGraph (Finset.univ.image (orientedWalkEdge t q))
  have hadjp (i : Fin n) : G.Adj (p i.castSucc) (p i.succ) := orientedWalk_step_adj s p hpl i
  have hadjq (i : Fin n) : H.Adj (q i.castSucc) (q i.succ) := orientedWalk_step_adj t q hql i
  rw [orientedTree_vertex_eq_iff_cuts s p hp,orientedTree_vertex_eq_iff_cuts t q hq]
  apply forall_congr'
  intro i
  refine boolPath_eq_iff_of_same_steps
    (fun x => bridgeCutColor G (p i.castSucc) (p i.succ) (p x))
    (fun x => bridgeCutColor H (q i.castSucc) (q i.succ) (q x)) ?_ a b
  intro j
  have hbp : G.IsBridge s(p i.castSucc,p i.succ) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hp.isAcyclic (hadjp i)
  have hbq : H.IsBridge s(q i.castSucc,q i.succ) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hq.isAcyclic (hadjq i)
  rw [bridgeCutColor_same_iff_other_edge G _ _ _ _ hbp (hadjp j),
    bridgeCutColor_same_iff_other_edge H _ _ _ _ hbq (hadjq j)]
  apply not_congr
  exact (orientedWalkEdge_eq_iff_geometric s p hpn j i).symm.trans
    ((he j i).trans (orientedWalkEdge_eq_iff_geometric t q hqn j i))

#print axioms orientedTree_vertex_pattern_of_edge_pattern
end SpectralRadiusUpperTail
