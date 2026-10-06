import SpectralRadiusUpperTail.TreeMatchingVertexDecoder
import SpectralRadiusUpperTail.WalkFamilyGluingPairs

namespace SpectralRadiusUpperTail
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {n : I → ℕ}

/-- A label-free local relation: two slots belong to the same tour and its
matching decoder identifies them. Different tours are kept separate here. -/
def matchingLocalRelation (f : ∀ i, Fin (n i) → Fin (n i))
    (x y : Σ i, Fin (n i+1)) : Prop :=
  ∃ i a b, x = ⟨i,a⟩ ∧ y = ⟨i,b⟩ ∧ matchingVertexSetoid (f i) a b

lemma matchingLocalRelation_eq_iff (f : ∀ i, Fin (n i) → Fin (n i))
    (p : ∀ i, Fin (n i+1) → V)
    (hp : ∀ i a b, p i a = p i b ↔ matchingVertexSetoid (f i) a b)
    (x y : Σ i, Fin (n i+1)) :
    walkFamilyLocalMap p x = walkFamilyLocalMap p y ↔ matchingLocalRelation f x y := by
  constructor
  · obtain ⟨i,a⟩ := x
    obtain ⟨j,b⟩ := y
    intro h
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have hab : p i a = p i b := by
      have hsub : (⟨p i a,⟨a,rfl⟩⟩ : Set.range (p i)) = ⟨p i b,⟨b,rfl⟩⟩ := by
        simpa only [walkFamilyLocalMap,Sigma.mk.inj_iff,heq_iff_eq,true_and] using h
      exact congrArg Subtype.val hsub
    exact ⟨i,a,b,rfl,rfl,(hp i a b).mp hab⟩
  · rintro ⟨i,a,b,rfl,rfl,hab⟩
    have hs : (⟨p i a,⟨a,rfl⟩⟩ : Set.range (p i)) = ⟨p i b,⟨b,rfl⟩⟩ :=
      Subtype.ext ((hp i a b).mpr hab)
    exact congrArg (Sigma.mk i) hs

#print axioms matchingLocalRelation
#print axioms matchingLocalRelation_eq_iff
end SpectralRadiusUpperTail
