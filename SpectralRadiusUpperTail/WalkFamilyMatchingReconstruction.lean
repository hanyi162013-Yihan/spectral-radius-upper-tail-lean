import SpectralRadiusUpperTail.WalkFamilyLocalEquality

namespace SpectralRadiusUpperTail
variable {I V W : Type*} [Fintype I] [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W] {n : I → ℕ}

/-- The local equal-entry matchings and the extra gluing pairs determine the
entire surviving vertex equality pattern, including cross-tour coincidences. -/
lemma walkFamily_pattern_of_matching_and_gluing
    (T : Finset (V × V)) (U : Finset (W × W))
    (ht : (walkSupportGraph T).IsTree) (hu : (walkSupportGraph U).IsTree)
    (htl : ∀ a b, (a,b) ∈ T → a ≠ b) (hul : ∀ a b, (a,b) ∈ U → a ≠ b)
    (htn : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (hun : ∀ a b, (a,b) ∈ U → (b,a) ∉ U)
    (s t : ∀ i, Fin (n i) → Bool)
    (p : ∀ i, Fin (n i+1) → V) (q : ∀ i, Fin (n i+1) → W)
    (hp : ∀ i, Finset.univ.image (orientedWalkEdge (s i) (p i)) ⊆ T)
    (hq : ∀ i, Finset.univ.image (orientedWalkEdge (t i) (q i)) ⊆ U)
    (hmp : ∀ i j, entryMultiplicity (orientedWalkEdge (s i) (p i))
      (orientedWalkEdge (s i) (p i) j) = 2)
    (hmq : ∀ i j, entryMultiplicity (orientedWalkEdge (t i) (q i))
      (orientedWalkEdge (t i) (q i) j) = 2)
    (f : ∀ i, Fin (n i) → Fin (n i)) (hfix : ∀ i j, f i j ≠ j)
    (hfp : ∀ i j, orientedWalkEdge (s i) (p i) (f i j) = orientedWalkEdge (s i) (p i) j)
    (hfq : ∀ i j, orientedWalkEdge (t i) (q i) (f i j) = orientedWalkEdge (t i) (q i) j)
    (E : Finset ((Σ i, Fin (n i+1)) × (Σ i, Fin (n i+1))))
    (hgp : ∀ x y, Relation.EqvGen
      (fun a b => walkFamilyLocalMap p a = walkFamilyLocalMap p b ∨ (a,b) ∈ E) x y ↔
        p x.1 x.2 = p y.1 y.2)
    (hgq : ∀ x y, Relation.EqvGen
      (fun a b => walkFamilyLocalMap q a = walkFamilyLocalMap q b ∨ (a,b) ∈ E) x y ↔
        q x.1 x.2 = q y.1 y.2)
    (x y : Σ i, Fin (n i+1)) :
    p x.1 x.2 = p y.1 y.2 ↔ q x.1 x.2 = q y.1 y.2 := by
  apply walkFamily_global_pattern_of_gluing p q _ E hgp hgq x y
  intro i a b
  exact ambientTree_vertex_pattern_of_matching T U ht hu htl hul htn hun
    (s i) (t i) (p i) (q i) (hp i) (hq i) (hmp i) (hmq i) (f i) (hfix i)
    (hfp i) (hfq i) a b

#print axioms walkFamily_pattern_of_matching_and_gluing
end SpectralRadiusUpperTail
