import SpectralRadiusUpperTail.DefectRouteLocalVertices
import SpectralRadiusUpperTail.WalkFamilyGluingBudget

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

/-- Primitive vertex slots retain their tour index; shared ambient vertices
are not identified until the gluing relation is applied. -/
abbrev DefectRouteCertificate.TourPosition (c : DefectRouteCertificate s v) :=
  Σ i : Fin (expandedDefectRoutes c.segments c.tours).length,
    Fin (((expandedDefectRoutes c.segments c.tours).get i).tokens.length+1)

noncomputable def DefectRouteCertificate.localVertexMap (c : DefectRouteCertificate s v) :=
  walkFamilyLocalMap (fun i => (c.localTourModel i).vertices)

/-- An actual defect-route certificate needs at most 8g additional pairs of
primitive vertex slots to recover every surviving vertex equality from the
individual tour equality relations. This permits shared intermediate vertices. -/
lemma DefectRouteCertificate.exists_gluing_pairs (c : DefectRouteCertificate s v) :
    ∃ E : Finset (c.TourPosition × c.TourPosition),
      E.card ≤ 8*(r+1-Fintype.card V) ∧
      ∀ x y, Relation.EqvGen
        (fun a b => c.localVertexMap a = c.localVertexMap b ∨ (a,b) ∈ E) x y ↔
        (c.localTourModel x.1).vertices x.2 = (c.localTourModel y.1).vertices y.2 := by
  classical
  let p := fun i => (c.localTourModel i).vertices
  obtain ⟨E,hcard,hrec⟩ := walkFamily_exists_gluing_pairs c.treeEntries c.tree
    c.no_loops c.no_opposites c.tourSigns p c.localTour_support c.localTour_entries_disjoint
  have hbudget := walkFamily_gluing_budget c.tourSigns p
  have hlen : Fintype.card (Fin (expandedDefectRoutes c.segments c.tours).length) ≤
      8*(r+1-Fintype.card V)+1 := by
    simp only [Fintype.card_fin,expandedDefectRoutes,List.length_map]
    exact c.tour_budget.trans c.segment_budget
  refine ⟨E,?_,hrec⟩
  omega

#print axioms DefectRouteCertificate.TourPosition
#print axioms DefectRouteCertificate.localVertexMap
#print axioms DefectRouteCertificate.exists_gluing_pairs
end SpectralRadiusUpperTail
