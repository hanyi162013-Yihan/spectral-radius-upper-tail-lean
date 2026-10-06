import SpectralRadiusUpperTail.IncreasingPathOrthogonality
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

namespace SpectralRadiusUpperTail

/-- A Schur block path with k strictly upper-triangular transitions. -/
abbrev IncreasingBlockPath (n k : ℕ) := {p : Fin (k+1) → Fin n // StrictMono p}

noncomputable def increasingPathVertexEquiv (n k : ℕ) :
    IncreasingBlockPath n k ≃ {s : Finset (Fin n) // s ∈ Finset.univ.powersetCard (k+1)} where
  toFun p := ⟨Finset.univ.image p.val, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      rw [Finset.card_image_of_injective _ p.property.injective]
      simp⟩⟩
  invFun s := ⟨s.val.orderEmbOfFin (Finset.mem_powersetCard.mp s.property).2,
    (s.val.orderEmbOfFin (Finset.mem_powersetCard.mp s.property).2).strictMono⟩
  left_inv p := by
    apply Subtype.ext
    apply (StrictMono.range_inj (Finset.orderEmbOfFin _ _).strictMono p.property).mp
    rw [Finset.range_orderEmbOfFin]
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ _ _

/-- Exact count, including the vanishing case k+1>n. -/
theorem increasingBlockPath_card (n k : ℕ) :
    Nat.card (IncreasingBlockPath n k) = n.choose (k+1) := by
  classical
  rw [Nat.card_congr (increasingPathVertexEquiv n k), Nat.card_eq_fintype_card,
    Fintype.card_coe, Finset.card_powersetCard]
  simp

#print axioms increasingPathVertexEquiv
#print axioms increasingBlockPath_card
end SpectralRadiusUpperTail
