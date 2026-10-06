import SpectralRadiusUpperTail.IndexedMatchingGluing
import SpectralRadiusUpperTail.IndexedOccurrenceCoverage
import SpectralRadiusUpperTail.OccurrenceFullReconstruction

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

/-- Complete equality reconstruction from occurrence words, local matchings,
and bounded gluing/restoration records. Occurrence words are themselves decoded
from deletion, length, and arrangement records in `decodePositionTours_eq`. -/
lemma DefectRouteCertificate.indexed_full_reconstruction (c : DefectRouteCertificate s v) :
    ∃ E : Finset (c.IndexedVertexSlot × c.IndexedVertexSlot),
      E.card ≤ 8*(r+1-Fintype.card V) ∧
    ∃ F : Finset (Fin (2*r+1) × Fin (2*r+1)),
      F.card ≤ 8*(r+1-Fintype.card V)+1 ∧
      ∀ x y, Relation.EqvGen (fun a b =>
        occurrencePullbackRelation s c.indexedWord
          (Relation.EqvGen (fun u w =>
            matchingLocalRelation (fun i => (c.indexedMatching i).val.val) u w ∨ (u,w) ∈ E)) a b ∨
          (a,b) ∈ F) x y ↔ v x = v y := by
  obtain ⟨E,hE,hrec⟩ := c.indexedMatching_gluing
  obtain ⟨F,hF,hfull⟩ := occurrence_exists_full_reconstruction s v c.deletedPositions
    c.indexedWord (fun i => (c.indexedPath i).vertices)
    (fun i j => (c.indexedPath i).entries j) c.indexedWord_coverage _ hrec
  exact ⟨E,hE,F,hF.trans (Nat.add_le_add_right c.deletion_budget 1),hfull⟩

#print axioms DefectRouteCertificate.indexed_full_reconstruction
end SpectralRadiusUpperTail
