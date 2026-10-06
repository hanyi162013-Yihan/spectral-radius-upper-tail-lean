import SpectralRadiusUpperTail.WalkFamilyGluingPairs

namespace SpectralRadiusUpperTail
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
variable {n : I → ℕ}

lemma walkFamily_component_pos [Nonempty I]
    (s : ∀ i, Fin (n i) → Bool) (p : ∀ i, Fin (n i+1) → V) :
    0 < Nat.card (walkSupportGraph
      (restrictedEntries (walkFamilyEntries s p) (walkFamilyVertices p))).ConnectedComponent := by
  classical
  let i : I := Classical.choice inferInstance
  let x : walkFamilyVertices p := ⟨p i 0,⟨⟨i,0⟩,rfl⟩⟩
  let G := walkSupportGraph (restrictedEntries (walkFamilyEntries s p) (walkFamilyVertices p))
  let : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk x⟩
  exact Nat.card_pos

lemma walkFamily_gluing_budget (s : ∀ i, Fin (n i) → Bool)
    (p : ∀ i, Fin (n i+1) → V) :
    Fintype.card I - Nat.card (walkSupportGraph
      (restrictedEntries (walkFamilyEntries s p) (walkFamilyVertices p))).ConnectedComponent
      ≤ Fintype.card I - 1 := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    have hc := walkFamily_component_pos s p
    omega

#print axioms walkFamily_component_pos
#print axioms walkFamily_gluing_budget
end SpectralRadiusUpperTail
