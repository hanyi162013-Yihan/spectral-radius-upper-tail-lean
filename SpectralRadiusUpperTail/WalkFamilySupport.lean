import SpectralRadiusUpperTail.VisitedWalkCardinality
import SpectralRadiusUpperTail.RestrictedDirectedSupport

namespace SpectralRadiusUpperTail
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
variable {n : I → ℕ}

noncomputable def walkFamilyEntries (s : ∀ i, Fin (n i) → Bool)
    (p : ∀ i, Fin (n i+1) → V) : Finset (V × V) := by
  classical
  exact Finset.univ.biUnion (fun i => Finset.univ.image (orientedWalkEdge (s i) (p i)))

def walkFamilyVertices (p : ∀ i, Fin (n i+1) → V) : Set V :=
  Set.range (fun x : Σ i, Fin (n i+1) => p x.1 x.2)

/-- The actual map from disjoint local visited supports onto their union.
Different tours may map different local vertices to the same ambient vertex. -/
def walkFamilyVertexMap (p : ∀ i, Fin (n i+1) → V)
    (x : Σ i, Set.range (p i)) : walkFamilyVertices p :=
  ⟨x.2.val, by
    obtain ⟨j,hj⟩ := x.2.property
    exact ⟨⟨x.1,j⟩,hj⟩⟩

lemma walkFamilyVertexMap_surjective (p : ∀ i, Fin (n i+1) → V) :
    Function.Surjective (walkFamilyVertexMap p) := by
  rintro ⟨v,⟨i,j⟩,rfl⟩
  exact ⟨⟨i,⟨p i j,⟨j,rfl⟩⟩⟩,rfl⟩

lemma walkFamilyEntries_endpoints (s : ∀ i, Fin (n i) → Bool)
    (p : ∀ i, Fin (n i+1) → V) :
    ∀ e ∈ walkFamilyEntries s p, e.1 ∈ walkFamilyVertices p ∧ e.2 ∈ walkFamilyVertices p := by
  classical
  intro e he
  obtain ⟨i,_,he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
  have ha : p i j.castSucc ∈ walkFamilyVertices p := ⟨⟨i,j.castSucc⟩,rfl⟩
  have hb : p i j.succ ∈ walkFamilyVertices p := ⟨⟨i,j.succ⟩,rfl⟩
  cases h : s i j <;> simp only [orientedWalkEdge,h,Bool.false_eq_true,if_false,if_true]
  · exact ⟨ha,hb⟩
  · exact ⟨hb,ha⟩

lemma walkFamilyEntries_subset (T : Finset (V × V))
    (s : ∀ i, Fin (n i) → Bool) (p : ∀ i, Fin (n i+1) → V)
    (hsub : ∀ i, Finset.univ.image (orientedWalkEdge (s i) (p i)) ⊆ T) :
    walkFamilyEntries s p ⊆ T := by
  classical
  intro e he
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
  exact hsub i hi

#print axioms walkFamilyEntries
#print axioms walkFamilyVertices
#print axioms walkFamilyVertexMap
#print axioms walkFamilyVertexMap_surjective
#print axioms walkFamilyEntries_endpoints
#print axioms walkFamilyEntries_subset
end SpectralRadiusUpperTail
