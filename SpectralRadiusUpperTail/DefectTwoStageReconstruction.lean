import SpectralRadiusUpperTail.RetainedTourTransport

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

/-- Pull the glued local relation back to original retained positions using
the actual transport. This transport is kept explicit in the reconstruction. -/
def DefectRouteCertificate.transportedGluingRelation (c : DefectRouteCertificate s v)
    (E : Finset (c.TourPosition × c.TourPosition)) (a b : Fin (2*r+1)) : Prop :=
  ∃ x y : retainedInitialPositions c.deletedPositions,
    x.val = a ∧ y.val = b ∧ Relation.EqvGen
      (fun u w => c.localVertexMap u = c.localVertexMap w ∨ (u,w) ∈ E)
      (c.retainedTransport x) (c.retainedTransport y)

lemma DefectRouteCertificate.transportedGluingRelation_iff (c : DefectRouteCertificate s v)
    (E : Finset (c.TourPosition × c.TourPosition))
    (hE : ∀ x y, Relation.EqvGen
      (fun a b => c.localVertexMap a = c.localVertexMap b ∨ (a,b) ∈ E) x y ↔
      (c.localTourModel x.1).vertices x.2 = (c.localTourModel y.1).vertices y.2)
    (a b : Fin (2*r+1)) : c.transportedGluingRelation E a b ↔
      a ∈ retainedInitialPositions c.deletedPositions ∧
      b ∈ retainedInitialPositions c.deletedPositions ∧ v a = v b := by
  constructor
  · rintro ⟨x,y,rfl,rfl,hxy⟩
    refine ⟨x.property,y.property,?_⟩
    have h := (hE _ _).mp hxy
    simpa only [c.retainedTransport_vertex] using h
  · rintro ⟨ha,hb,hab⟩
    refine ⟨⟨a,ha⟩,⟨b,hb⟩,rfl,rfl,?_⟩
    apply (hE _ _).mpr
    simpa only [c.retainedTransport_vertex] using hab

/-- Complete equality reconstruction in two stages: at most 8g local gluing
pairs and at most 8g+1 original-position restoration pairs. This is NOT yet a
bounded canonical code: the explicit retained transport must still be encoded
economically through segment ordering, reversals, and cuts. -/
lemma DefectRouteCertificate.exists_two_stage_reconstruction (c : DefectRouteCertificate s v) :
    ∃ E : Finset (c.TourPosition × c.TourPosition), E.card ≤ 8*(r+1-Fintype.card V) ∧
    ∃ F : Finset (Fin (2*r+1) × Fin (2*r+1)), F.card ≤ 8*(r+1-Fintype.card V)+1 ∧
      ∀ x y, Relation.EqvGen
        (fun a b => c.transportedGluingRelation E a b ∨ (a,b) ∈ F) x y ↔ v x = v y := by
  obtain ⟨E,hE,hrec⟩ := c.exists_gluing_pairs
  obtain ⟨F,hF,hfull⟩ := c.original_position_extension
  refine ⟨E,hE,F,hF,?_⟩
  have he : (fun a b => c.transportedGluingRelation E a b ∨ (a,b) ∈ F) =
      (fun a b => (a ∈ retainedInitialPositions c.deletedPositions ∧
        b ∈ retainedInitialPositions c.deletedPositions ∧ v a = v b) ∨ (a,b) ∈ F) := by
    funext a b
    exact propext (or_congr (c.transportedGluingRelation_iff E hrec a b) Iff.rfl)
  simpa only [he] using hfull

#print axioms DefectRouteCertificate.transportedGluingRelation
#print axioms DefectRouteCertificate.transportedGluingRelation_iff
#print axioms DefectRouteCertificate.exists_two_stage_reconstruction
end SpectralRadiusUpperTail
