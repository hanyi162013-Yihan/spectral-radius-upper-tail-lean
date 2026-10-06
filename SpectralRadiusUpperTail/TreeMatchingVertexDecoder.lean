import SpectralRadiusUpperTail.MatchingVertexDecoder
import SpectralRadiusUpperTail.AmbientMatchingReconstruction

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

lemma visitedWalk_entryMultiplicity (s : Fin n → Bool) (p : Fin (n+1) → V) (i : Fin n) :
    entryMultiplicity (orientedWalkEdge s (visitedWalkPath p))
      (orientedWalkEdge s (visitedWalkPath p) i) =
    entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) := by
  unfold entryMultiplicity
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,visitedWalkEdge_eq_iff]

/-- The matching decodes the complete local vertex pattern by deterministic
Boolean cut traces; ambient vertex labels do not occur in the decoder. -/
lemma orientedTree_vertex_eq_matchingDecoder
    (s : Fin n → Bool) (p : Fin (n+1) → V)
    (ht : (walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))).IsTree)
    (hloop : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ Finset.univ.image (orientedWalkEdge s p) → (b,a) ∉
      Finset.univ.image (orientedWalkEdge s p))
    (hm : ∀ i, entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) = 2)
    (f : Fin n → Fin n) (hfix : ∀ i, f i ≠ i)
    (hf : ∀ i, orientedWalkEdge s p (f i) = orientedWalkEdge s p i)
    (a b : Fin (n+1)) : p a = p b ↔ matchingVertexSetoid f a b := by
  let G := walkSupportGraph (Finset.univ.image (orientedWalkEdge s p))
  have hadj (i : Fin n) : G.Adj (p i.castSucc) (p i.succ) :=
    orientedWalk_step_adj s p hloop i
  rw [orientedTree_vertex_eq_iff_cuts s p ht,matchingVertexSetoid_iff]
  apply forall_congr'
  intro i
  apply boolPath_eq_iff_of_same_steps
    (fun x => bridgeCutColor G (p i.castSucc) (p i.succ) (p x))
    (matchingVertexColor f i) _ a b
  intro j
  have hb : G.IsBridge s(p i.castSucc,p i.succ) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic (hadj i)
  rw [bridgeCutColor_same_iff_other_edge G _ _ _ _ hb (hadj j),matchingVertexColor_step]
  apply not_congr
  exact (orientedWalkEdge_eq_iff_geometric s p hno j i).symm.trans
    (doubleWord_entry_eq_iff_matching (orientedWalkEdge s p) hm f hfix hf i j)

lemma ambientTree_vertex_eq_matchingDecoder
    (T : Finset (V × V)) (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : Fin n → Bool) (p : Fin (n+1) → V)
    (hp : Finset.univ.image (orientedWalkEdge s p) ⊆ T)
    (hm : ∀ i, entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) = 2)
    (f : Fin n → Fin n) (hfix : ∀ i, f i ≠ i)
    (hf : ∀ i, orientedWalkEdge s p (f i) = orientedWalkEdge s p i)
    (a b : Fin (n+1)) : p a = p b ↔ matchingVertexSetoid f a b := by
  classical
  have h := orientedTree_vertex_eq_matchingDecoder s (visitedWalkPath p)
    (visitedWalkSupport_isTree T ht s p hp)
    (fun x y hxy he => hloop x.val y.val (hp (visitedWalkEntry_mem s p hxy)) (congrArg Subtype.val he))
    (fun x y hxy hyx => hno x.val y.val (hp (visitedWalkEntry_mem s p hxy))
      (hp (visitedWalkEntry_mem s p hyx)))
    (fun i => (visitedWalk_entryMultiplicity s p i).trans (hm i)) f hfix
    (fun i => (visitedWalkEdge_eq_iff s p (f i) i).mpr (hf i)) a b
  constructor
  · intro hab
    exact h.mp (Subtype.ext hab)
  · intro hab
    exact congrArg Subtype.val (h.mpr hab)

#print axioms visitedWalk_entryMultiplicity
#print axioms orientedTree_vertex_eq_matchingDecoder
#print axioms ambientTree_vertex_eq_matchingDecoder
end SpectralRadiusUpperTail
