import SpectralRadiusUpperTail.PartialKernelExtension
import SpectralRadiusUpperTail.DefectRouteCertificate

namespace SpectralRadiusUpperTail

/-- Original initial vertex positions of retained steps. Terminal positions
may also be known; using this smaller set gives a uniform D+1 budget. -/
def retainedInitialPositions {n : ℕ} (D : Finset (Fin n)) : Finset (Fin (n+1)) :=
  Dᶜ.image Fin.castSucc

lemma retainedInitialPositions_card {n : ℕ} (D : Finset (Fin n)) :
    (retainedInitialPositions D).card = n - D.card := by
  rw [retainedInitialPositions,Finset.card_image_of_injective _ (Fin.castSucc_injective n),
    Finset.card_compl,Fintype.card_fin]

lemma retainedInitialPositions_missing {n : ℕ} (D : Finset (Fin n)) :
    Fintype.card (Fin (n+1)) - (retainedInitialPositions D).card = D.card+1 := by
  have h : D.card ≤ n := by simpa using D.card_le_univ
  rw [retainedInitialPositions_card,Fintype.card_fin]
  omega

/-- The original chronological equality pattern can be extended from retained
initial positions using at most D+1 additional pairs of original positions. -/
lemma original_position_extension {n : ℕ} {V : Type*}
    (v : Fin (n+1) → V) (D : Finset (Fin n)) :
    ∃ E : Finset (Fin (n+1) × Fin (n+1)), E.card ≤ D.card+1 ∧
      ∀ x y, Relation.EqvGen
        (fun a b => (a ∈ retainedInitialPositions D ∧ b ∈ retainedInitialPositions D ∧
          v a = v b) ∨ (a,b) ∈ E) x y ↔ v x = v y := by
  simpa only [retainedInitialPositions_missing] using
    exists_partial_kernel_extension v (retainedInitialPositions D)

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.deletedPositions (c : DefectRouteCertificate s v) :
    Finset (Fin (2*r)) :=
  Finset.univ.filter (fun i => entryMultiplicity (orientedWalkEdge s v)
    (orientedWalkEdge s v i) ≠ 2 ∨ orientedWalkEdge s v i ∉ c.treeEntries)

/-- Actual certificate endpoint restoration costs at most 8g+1 pairs.
The remaining task is to transport its retained relation through the route code. -/
lemma DefectRouteCertificate.original_position_extension (c : DefectRouteCertificate s v) :
    ∃ E : Finset (Fin (2*r+1) × Fin (2*r+1)), E.card ≤ 8*(r+1-Fintype.card V)+1 ∧
      ∀ x y, Relation.EqvGen
        (fun a b => (a ∈ retainedInitialPositions c.deletedPositions ∧
          b ∈ retainedInitialPositions c.deletedPositions ∧ v a = v b) ∨ (a,b) ∈ E) x y ↔
        v x = v y := by
  obtain ⟨E,hE,hrec⟩ := SpectralRadiusUpperTail.original_position_extension v c.deletedPositions
  exact ⟨E,hE.trans (Nat.add_le_add_right c.deletion_budget 1),hrec⟩

#print axioms retainedInitialPositions
#print axioms retainedInitialPositions_card
#print axioms retainedInitialPositions_missing
#print axioms original_position_extension
#print axioms DefectRouteCertificate.deletedPositions
#print axioms DefectRouteCertificate.original_position_extension
end SpectralRadiusUpperTail
