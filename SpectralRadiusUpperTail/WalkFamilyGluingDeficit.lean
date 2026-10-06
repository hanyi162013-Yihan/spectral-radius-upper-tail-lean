import SpectralRadiusUpperTail.WalkFamilySupport
import SpectralRadiusUpperTail.OrientedForestCardinality
import SpectralRadiusUpperTail.FiniteFiberGluing

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
variable {n : I → ℕ}

/-- Total local vertices = retained entries + number of tours, when distinct
tours have disjoint directed-entry supports. Shared vertices are allowed. -/
lemma walkFamily_local_vertex_card (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : ∀ i, Fin (n i) → Bool) (p : ∀ i, Fin (n i+1) → V)
    (hsub : ∀ i, Finset.univ.image (orientedWalkEdge (s i) (p i)) ⊆ T)
    (hdis : Pairwise (fun i j => Disjoint
      (Finset.univ.image (orientedWalkEdge (s i) (p i)))
      (Finset.univ.image (orientedWalkEdge (s j) (p j))))) :
    Nat.card (Σ i, Set.range (p i)) = (walkFamilyEntries s p).card + Fintype.card I := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hc : ∀ i, Fintype.card (Set.range (p i)) =
      (Finset.univ.image (orientedWalkEdge (s i) (p i))).card + 1 := by
    intro i
    simpa only [Nat.card_eq_fintype_card] using
      visitedWalk_card_eq_entries_add_one T ht hloop hno (s i) (p i) (hsub i)
  simp_rw [hc]
  rw [Finset.sum_add_distrib]
  have he : (walkFamilyEntries s p).card =
      ∑ i, (Finset.univ.image (orientedWalkEdge (s i) (p i))).card :=
    Finset.card_biUnion (fun i _ j _ hij => hdis hij)
  rw [← he]
  simp

/-- The union support has exactly retained entries plus forest components many
vertices. Restricting to visited vertices avoids counting ambient isolated ones. -/
lemma walkFamily_union_vertex_card (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : ∀ i, Fin (n i) → Bool) (p : ∀ i, Fin (n i+1) → V)
    (hsub : ∀ i, Finset.univ.image (orientedWalkEdge (s i) (p i)) ⊆ T) :
    Nat.card (walkFamilyVertices p) = (walkFamilyEntries s p).card +
      Nat.card (walkSupportGraph (restrictedEntries (walkFamilyEntries s p)
        (walkFamilyVertices p))).ConnectedComponent := by
  classical
  have hE := walkFamilyEntries_subset T s p hsub
  have ha : (walkSupportGraph (walkFamilyEntries s p)).IsAcyclic :=
    ht.isAcyclic.anti (walkSupportGraph_mono hE)
  have h := oriented_forest_card (restrictedEntries (walkFamilyEntries s p) (walkFamilyVertices p))
    (restrictedEntries_isAcyclic _ _ ha)
    (fun a b hab he => hloop a.val b.val (hE (Finset.mem_filter.mp hab).2) (congrArg Subtype.val he))
    (fun a b hab hba => hno a.val b.val (hE (Finset.mem_filter.mp hab).2)
      (hE (Finset.mem_filter.mp hba).2))
  rw [restrictedEntries_card _ _ (walkFamilyEntries_endpoints s p)] at h
  simpa only [Nat.card_eq_fintype_card] using h

/-- The exact excess of disjoint local vertices over actual surviving vertices
is t-c, not zero: different closed tours may share intermediate vertices. -/
lemma walkFamily_gluing_deficit (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : ∀ i, Fin (n i) → Bool) (p : ∀ i, Fin (n i+1) → V)
    (hsub : ∀ i, Finset.univ.image (orientedWalkEdge (s i) (p i)) ⊆ T)
    (hdis : Pairwise (fun i j => Disjoint
      (Finset.univ.image (orientedWalkEdge (s i) (p i)))
      (Finset.univ.image (orientedWalkEdge (s j) (p j))))) :
    Nat.card (Σ i, Set.range (p i)) - Nat.card (walkFamilyVertices p) =
      Fintype.card I - Nat.card (walkSupportGraph
        (restrictedEntries (walkFamilyEntries s p) (walkFamilyVertices p))).ConnectedComponent := by
  rw [walkFamily_local_vertex_card T ht hloop hno s p hsub hdis,
    walkFamily_union_vertex_card T ht hloop hno s p hsub]
  omega

#print axioms walkFamily_local_vertex_card
#print axioms walkFamily_union_vertex_card
#print axioms walkFamily_gluing_deficit
end SpectralRadiusUpperTail
