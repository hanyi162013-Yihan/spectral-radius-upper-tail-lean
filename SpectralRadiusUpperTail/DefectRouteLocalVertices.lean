import SpectralRadiusUpperTail.TreeRouteLocalVertices
import SpectralRadiusUpperTail.UniqueDoubleEntryTour

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.localTourModel (c : DefectRouteCertificate s v)
    (i : Fin (expandedDefectRoutes c.segments c.tours).length) :
    TreeRouteLocalVertices ((expandedDefectRoutes c.segments c.tours).get i) :=
  Classical.choice (treeRoute_local_vertices c.treeEntries c.tree c.no_loops c.no_opposites
    _ (c.closed_routes _ (List.get_mem _ i)).1.1
    (c.route_entry_support _ (List.get_mem _ i)))

def DefectRouteCertificate.tourSigns (c : DefectRouteCertificate s v)
    (i : Fin (expandedDefectRoutes c.segments c.tours).length) :
    Fin ((expandedDefectRoutes c.segments c.tours).get i).tokens.length → Bool :=
  fun j => (((expandedDefectRoutes c.segments c.tours).get i).tokens.get j).2

lemma DefectRouteCertificate.localTour_support (c : DefectRouteCertificate s v)
    (i : Fin (expandedDefectRoutes c.segments c.tours).length) :
    Finset.univ.image (orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices) ⊆ c.treeEntries := by
  intro e he
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
  have heq := (c.localTourModel i).entries j
  change orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices j = _ at heq
  rw [heq]
  exact c.route_entry_support _ (List.get_mem _ i) _ (List.get_mem _ j)

lemma DefectRouteCertificate.localTour_entry_count (c : DefectRouteCertificate s v)
    (i : Fin (expandedDefectRoutes c.segments c.tours).length) (e : V × V)
    (he : e ∈ Finset.univ.image (orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices)) :
    ((((expandedDefectRoutes c.segments c.tours).get i).tokens).map Prod.fst).count e = 2 := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
  have heq := (c.localTourModel i).entries j
  change orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices j = _ at heq
  rw [heq]
  exact c.route_double_entries _ (List.get_mem _ i) _ (List.get_mem _ j)

/-- Entry supports of different indexed tours are disjoint. This deliberately
does not assert that their vertex supports are disjoint. -/
lemma DefectRouteCertificate.localTour_entries_disjoint (c : DefectRouteCertificate s v) :
    Pairwise (fun i j => Disjoint
      (Finset.univ.image (orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices))
      (Finset.univ.image (orientedWalkEdge (c.tourSigns j) (c.localTourModel j).vertices))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hi := c.localTour_entry_count i e hei
  have hj := c.localTour_entry_count j e hej
  have hpos : 0 < ((expandedDefectRoutes c.segments c.tours).flatMap
      (fun p => p.tokens.map Prod.fst)).count e := by
    have hle := list_count_le_flatMap_of_mem (fun p : SegmentRoute V (V × V) => p.tokens.map Prod.fst)
      (expandedDefectRoutes c.segments c.tours) _ (List.get_mem _ i) e
    omega
  have hret : e ∈ c.treeEntries ∧ entryMultiplicity (orientedWalkEdge s v) e = 2 := by
    rw [c.total_entry_counts e] at hpos
    split_ifs at hpos with h
    · exact h
    · omega
  obtain ⟨k,_,hk⟩ := c.unique_entry_tour e hret
  exact hij ((hk i hi).trans (hk j hj).symm)

#print axioms DefectRouteCertificate.localTourModel
#print axioms DefectRouteCertificate.tourSigns
#print axioms DefectRouteCertificate.localTour_support
#print axioms DefectRouteCertificate.localTour_entry_count
#print axioms DefectRouteCertificate.localTour_entries_disjoint
end SpectralRadiusUpperTail
