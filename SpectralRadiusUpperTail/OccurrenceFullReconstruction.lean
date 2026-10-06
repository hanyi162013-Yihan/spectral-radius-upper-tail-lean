import SpectralRadiusUpperTail.OccurrenceVertexTransport

namespace SpectralRadiusUpperTail
variable {I V : Type*} {L : ℕ} {n : I → ℕ}

/-- The occurrence-based decoder needs only D+1 additional original-position
pairs to recover the complete chronological equality pattern. -/
lemma occurrence_exists_full_reconstruction (s : Fin L → Bool) (v : Fin (L+1) → V)
    (D : Finset (Fin L)) (words : ∀ i, Fin (n i) → Fin L × Bool)
    (p : ∀ i, Fin (n i+1) → V)
    (he : ∀ i j, orientedWalkEdge (fun a => (words i a).2) (p i) j =
      orientedWalkEdge s v (words i j).1)
    (hwords : ∀ k, (∃ i j, (words i j).1 = k) ↔ k ∉ D)
    (R : (Σ i, Fin (n i+1)) → (Σ i, Fin (n i+1)) → Prop)
    (hR : ∀ x y, R x y ↔ p x.1 x.2 = p y.1 y.2) :
    ∃ F : Finset (Fin (L+1) × Fin (L+1)), F.card ≤ D.card+1 ∧
      ∀ x y, Relation.EqvGen
        (fun a b => occurrencePullbackRelation s words R a b ∨ (a,b) ∈ F) x y ↔ v x = v y := by
  obtain ⟨F,hF,hrec⟩ := original_position_extension v D
  refine ⟨F,hF,?_⟩
  have hh : (fun a b => occurrencePullbackRelation s words R a b ∨ (a,b) ∈ F) =
      (fun a b => (a ∈ retainedInitialPositions D ∧ b ∈ retainedInitialPositions D ∧
        v a = v b) ∨ (a,b) ∈ F) := by
    funext a b
    exact propext (or_congr (occurrencePullbackRelation_iff s v D words p he hwords R hR a b) Iff.rfl)
  simpa only [hh] using hrec

#print axioms occurrence_exists_full_reconstruction
end SpectralRadiusUpperTail
