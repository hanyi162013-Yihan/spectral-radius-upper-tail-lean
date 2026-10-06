import SpectralRadiusUpperTail.DirectedComponentCardinality

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Euler's finite-forest identity, retaining isolated vertices as components. -/
lemma oriented_forest_card (E : Finset (V × V))
    (ha : (walkSupportGraph E).IsAcyclic)
    (hloop : ∀ a b, (a,b) ∈ E → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ E → (b,a) ∉ E) :
    Fintype.card V = E.card + Nat.card (walkSupportGraph E).ConnectedComponent := by
  classical
  let G := walkSupportGraph E
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hv : (∑ c : G.ConnectedComponent, Nat.card c) = Fintype.card V := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
    rw [Fintype.card_sigma] at h
    calc
      (∑ c : G.ConnectedComponent, Nat.card c) =
          ∑ c : G.ConnectedComponent, Fintype.card {x : V // G.connectedComponentMk x = c} := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_congr (show c ≃ {x : V // G.connectedComponentMk x = c} from Equiv.refl _)
      _ = Fintype.card V := h
  have he : E.card = ∑ c : G.ConnectedComponent,
      (componentEntryFiber E c).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [← hv]
  simp_rw [oriented_forest_component_card E ha hloop hno]
  rw [Finset.sum_add_distrib, ← he]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  congr 1
  exact (Nat.card_eq_fintype_card (α := G.ConnectedComponent)).symm

#print axioms oriented_forest_card
end SpectralRadiusUpperTail
