import SpectralRadiusUpperTail.IndexedTourEntryDisjoint
import SpectralRadiusUpperTail.MatchingFamilyGluing

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

abbrev DefectRouteCertificate.IndexedVertexSlot (c : DefectRouteCertificate s v) :=
  Σ i : Fin c.indexedTours.length, Fin ((c.indexedTours.get i).tokens.length+1)

/-- Local matching decoders plus at most 8g pairs recover all shared vertices,
with original occurrence labels retained in the underlying tour words. -/
lemma DefectRouteCertificate.indexedMatching_gluing (c : DefectRouteCertificate s v) :
    ∃ E : Finset (c.IndexedVertexSlot × c.IndexedVertexSlot),
      E.card ≤ 8*(r+1-Fintype.card V) ∧
      ∀ x y, Relation.EqvGen
        (fun a b => matchingLocalRelation (fun i => (c.indexedMatching i).val.val) a b ∨
          (a,b) ∈ E) x y ↔ (c.indexedPath x.1).vertices x.2 = (c.indexedPath y.1).vertices y.2 := by
  obtain ⟨E,hcard,hrec⟩ := matchingFamily_exists_gluing c.treeEntries c.tree
    c.no_loops c.no_opposites c.indexedSigns (fun i => (c.indexedPath i).vertices)
    c.indexedPath_support c.indexedPath_entries_disjoint
    (fun i => (c.indexedMatching i).val.val) c.indexedMatching_decoder
  have hlen : Fintype.card (Fin c.indexedTours.length) ≤ 8*(r+1-Fintype.card V)+1 := by
    simp only [Fintype.card_fin,DefectRouteCertificate.indexedTours,List.length_map]
    exact c.tour_budget.trans c.segment_budget
  exact ⟨E,by omega,hrec⟩

#print axioms DefectRouteCertificate.IndexedVertexSlot
#print axioms DefectRouteCertificate.indexedMatching_gluing
end SpectralRadiusUpperTail
