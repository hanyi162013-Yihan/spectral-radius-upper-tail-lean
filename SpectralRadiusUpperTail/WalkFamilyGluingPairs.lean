import SpectralRadiusUpperTail.WalkFamilyGluingDeficit
import SpectralRadiusUpperTail.LiftedFiberGluing

namespace SpectralRadiusUpperTail
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
variable {n : I → ℕ}

/-- Map primitive vertex positions to their local-tour vertex classes. -/
def walkFamilyLocalMap (p : ∀ i, Fin (n i+1) → V)
    (x : Σ i, Fin (n i+1)) : Σ i, Set.range (p i) :=
  ⟨x.1,⟨p x.1 x.2,⟨x.2,rfl⟩⟩⟩

lemma walkFamilyLocalMap_surjective (p : ∀ i, Fin (n i+1) → V) :
    Function.Surjective (walkFamilyLocalMap p) := by
  rintro ⟨i,v,j,rfl⟩
  exact ⟨⟨i,j⟩,rfl⟩

/-- All cross-tour identifications can be restored by t-c pairs of original
primitive positions, together with the already known local vertex equalities. -/
lemma walkFamily_exists_gluing_pairs (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : ∀ i, Fin (n i) → Bool) (p : ∀ i, Fin (n i+1) → V)
    (hsub : ∀ i, Finset.univ.image (orientedWalkEdge (s i) (p i)) ⊆ T)
    (hdis : Pairwise (fun i j => Disjoint
      (Finset.univ.image (orientedWalkEdge (s i) (p i)))
      (Finset.univ.image (orientedWalkEdge (s j) (p j))))) :
    ∃ E : Finset ((Σ i, Fin (n i+1)) × (Σ i, Fin (n i+1))),
      E.card = Fintype.card I - Nat.card (walkSupportGraph
        (restrictedEntries (walkFamilyEntries s p) (walkFamilyVertices p))).ConnectedComponent ∧
      ∀ x y, Relation.EqvGen
        (fun a b => walkFamilyLocalMap p a = walkFamilyLocalMap p b ∨ (a,b) ∈ E) x y ↔
        p x.1 x.2 = p y.1 y.2 := by
  classical
  obtain ⟨E,hcard,hrec⟩ := exists_lifted_fiber_gluing
    (walkFamilyLocalMap p) (walkFamilyLocalMap_surjective p)
    (walkFamilyVertexMap p) (walkFamilyVertexMap_surjective p)
  have hd := walkFamily_gluing_deficit T ht hloop hno s p hsub hdis
  simp only [Nat.card_eq_fintype_card] at hd
  refine ⟨E,?_,?_⟩
  · simpa only [Nat.card_eq_fintype_card] using hcard.trans hd
  · intro x y
    exact (hrec x y).trans Subtype.ext_iff

#print axioms walkFamilyLocalMap
#print axioms walkFamilyLocalMap_surjective
#print axioms walkFamily_exists_gluing_pairs
end SpectralRadiusUpperTail
