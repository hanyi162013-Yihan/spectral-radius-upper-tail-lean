import SpectralRadiusUpperTail.MatchingLocalRelation
import SpectralRadiusUpperTail.WalkFamilyGluingBudget

namespace SpectralRadiusUpperTail
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {n : I → ℕ}

/-- Replace all local vertex labels in forest gluing by matching cut decoders.
The only extra data are at most one fewer pair than the number of tours. -/
lemma matchingFamily_exists_gluing (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (s : ∀ i, Fin (n i) → Bool) (p : ∀ i, Fin (n i+1) → V)
    (hsub : ∀ i, Finset.univ.image (orientedWalkEdge (s i) (p i)) ⊆ T)
    (hdis : Pairwise (fun i j => Disjoint
      (Finset.univ.image (orientedWalkEdge (s i) (p i)))
      (Finset.univ.image (orientedWalkEdge (s j) (p j)))))
    (f : ∀ i, Fin (n i) → Fin (n i))
    (hf : ∀ i a b, p i a = p i b ↔ matchingVertexSetoid (f i) a b) :
    ∃ E : Finset ((Σ i, Fin (n i+1)) × (Σ i, Fin (n i+1))),
      E.card ≤ Fintype.card I - 1 ∧
      ∀ x y, Relation.EqvGen (fun a b => matchingLocalRelation f a b ∨ (a,b) ∈ E) x y ↔
        p x.1 x.2 = p y.1 y.2 := by
  obtain ⟨E,hcard,hrec⟩ := walkFamily_exists_gluing_pairs T ht hloop hno s p hsub hdis
  refine ⟨E,hcard.le.trans (walkFamily_gluing_budget s p),?_⟩
  have he : (fun a b => matchingLocalRelation f a b ∨ (a,b) ∈ E) =
      (fun a b => walkFamilyLocalMap p a = walkFamilyLocalMap p b ∨ (a,b) ∈ E) := by
    funext a b
    exact propext (or_congr (matchingLocalRelation_eq_iff f p hf a b).symm Iff.rfl)
  simpa only [he] using hrec

#print axioms matchingFamily_exists_gluing
end SpectralRadiusUpperTail
