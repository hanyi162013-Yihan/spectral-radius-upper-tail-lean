import SpectralRadiusUpperTail.VisitedWalkSupport
import SpectralRadiusUpperTail.MatchingVertexReconstruction

namespace SpectralRadiusUpperTail
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] {n : ℕ}

lemma visitedWalkEdge_eq_iff (s : Fin n → Bool) (p : Fin (n+1) → V) (i j : Fin n) :
    orientedWalkEdge s (visitedWalkPath p) i = orientedWalkEdge s (visitedWalkPath p) j ↔
    orientedWalkEdge s p i = orientedWalkEdge s p j := by
  constructor
  · intro h
    have h' := congrArg (Prod.map Subtype.val Subtype.val) h
    simpa only [visitedWalkEdge_val] using h'
  · intro h
    have h' : Prod.map Subtype.val Subtype.val (orientedWalkEdge s (visitedWalkPath p) i) =
        Prod.map Subtype.val Subtype.val (orientedWalkEdge s (visitedWalkPath p) j) := by
      simpa only [visitedWalkEdge_val] using h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))

lemma visitedWalkEntry_mem (s : Fin n → Bool) (p : Fin (n+1) → V)
    {x y : Set.range p}
    (h : (x,y) ∈ Finset.univ.image (orientedWalkEdge s (visitedWalkPath p))) :
    (x.val,y.val) ∈ Finset.univ.image (orientedWalkEdge s p) := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
  refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
  have h' := congrArg (Prod.map Subtype.val Subtype.val) hi
  simpa only [visitedWalkEdge_val, Prod.map_apply] using h'

/-- Equal edge-occurrence patterns determine the vertex pattern for paths
inside ambient trees, without any assumption of visiting every ambient vertex. -/
lemma ambientTree_vertex_pattern_of_edge_pattern
    (T : Finset (V × V)) (U : Finset (W × W))
    (ht : (walkSupportGraph T).IsTree) (hu : (walkSupportGraph U).IsTree)
    (htl : ∀ a b, (a,b) ∈ T → a ≠ b) (hul : ∀ a b, (a,b) ∈ U → a ≠ b)
    (htn : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (hun : ∀ a b, (a,b) ∈ U → (b,a) ∉ U)
    (s t : Fin n → Bool) (p : Fin (n+1) → V) (q : Fin (n+1) → W)
    (hp : Finset.univ.image (orientedWalkEdge s p) ⊆ T)
    (hq : Finset.univ.image (orientedWalkEdge t q) ⊆ U)
    (he : ∀ i j, orientedWalkEdge s p i = orientedWalkEdge s p j ↔
      orientedWalkEdge t q i = orientedWalkEdge t q j)
    (a b : Fin (n+1)) : p a = p b ↔ q a = q b := by
  classical
  have h := orientedTree_vertex_pattern_of_edge_pattern s t
    (visitedWalkPath p) (visitedWalkPath q)
    (visitedWalkSupport_isTree T ht s p hp) (visitedWalkSupport_isTree U hu t q hq)
    (fun x y hxy hEq => htl x.val y.val (hp (visitedWalkEntry_mem s p hxy)) (congrArg Subtype.val hEq))
    (fun x y hxy hEq => hul x.val y.val (hq (visitedWalkEntry_mem t q hxy)) (congrArg Subtype.val hEq))
    (fun x y hxy hyx => htn x.val y.val (hp (visitedWalkEntry_mem s p hxy)) (hp (visitedWalkEntry_mem s p hyx)))
    (fun x y hxy hyx => hun x.val y.val (hq (visitedWalkEntry_mem t q hxy)) (hq (visitedWalkEntry_mem t q hyx)))
    (fun i j => (visitedWalkEdge_eq_iff s p i j).trans
      ((he i j).trans (visitedWalkEdge_eq_iff t q i j).symm)) a b
  constructor
  · intro hab
    exact congrArg Subtype.val (h.mp (Subtype.ext hab))
  · intro hab
    exact congrArg Subtype.val (h.mpr (Subtype.ext hab))

/-- The actual equal-entry matching therefore reconstructs each local tour's
vertex equality relation, even if that tour does not cover the ambient tree. -/
lemma ambientTree_vertex_pattern_of_matching
    (T : Finset (V × V)) (U : Finset (W × W))
    (ht : (walkSupportGraph T).IsTree) (hu : (walkSupportGraph U).IsTree)
    (htl : ∀ a b, (a,b) ∈ T → a ≠ b) (hul : ∀ a b, (a,b) ∈ U → a ≠ b)
    (htn : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (hun : ∀ a b, (a,b) ∈ U → (b,a) ∉ U)
    (s t : Fin n → Bool) (p : Fin (n+1) → V) (q : Fin (n+1) → W)
    (hp : Finset.univ.image (orientedWalkEdge s p) ⊆ T)
    (hq : Finset.univ.image (orientedWalkEdge t q) ⊆ U)
    (hmp : ∀ i, entryMultiplicity (orientedWalkEdge s p) (orientedWalkEdge s p i) = 2)
    (hmq : ∀ i, entryMultiplicity (orientedWalkEdge t q) (orientedWalkEdge t q i) = 2)
    (f : Fin n → Fin n) (hfix : ∀ i, f i ≠ i)
    (hfp : ∀ i, orientedWalkEdge s p (f i) = orientedWalkEdge s p i)
    (hfq : ∀ i, orientedWalkEdge t q (f i) = orientedWalkEdge t q i)
    (a b : Fin (n+1)) : p a = p b ↔ q a = q b := by
  apply ambientTree_vertex_pattern_of_edge_pattern T U ht hu htl hul htn hun
    s t p q hp hq _ a b
  intro i j
  exact (doubleWord_entry_eq_iff_matching (orientedWalkEdge s p) hmp f hfix hfp j i).trans
    (doubleWord_entry_eq_iff_matching (orientedWalkEdge t q) hmq f hfix hfq j i).symm

#print axioms visitedWalkEntry_mem
#print axioms visitedWalkEdge_eq_iff
#print axioms ambientTree_vertex_pattern_of_edge_pattern
#print axioms ambientTree_vertex_pattern_of_matching
end SpectralRadiusUpperTail
