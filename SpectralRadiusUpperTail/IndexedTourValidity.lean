import SpectralRadiusUpperTail.DefectIndexedTours
import SpectralRadiusUpperTail.SegmentRoutePayload

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.indexedTours_mapPayload (c : DefectRouteCertificate s v) :
    c.indexedTours.map (SegmentRoute.mapPayload (orientedWalkEdge s v)) =
      expandedDefectRoutes c.segments c.tours := by
  have hw : (fun i => (c.positionWords i).map (mapSegmentToken (orientedWalkEdge s v))) =
      (fun i => (c.segments.get i).tokens) := funext c.positionWords_payloads
  simp only [DefectRouteCertificate.indexedTours,List.map_map,Function.comp_def,
    expandSegmentRoute_mapPayload,hw,expandedDefectRoutes]

lemma DefectRouteCertificate.indexedTour_valid (c : DefectRouteCertificate s v)
    (p : SegmentRoute V (Fin (2*r))) (hp : p ∈ c.indexedTours) :
    p.Valid (orientedWalkEdge s v) ∧ p.start = p.finish := by
  have hmem : p.mapPayload (orientedWalkEdge s v) ∈ expandedDefectRoutes c.segments c.tours := by
    rw [← c.indexedTours_mapPayload]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have h := c.closed_routes _ hmem
  exact ⟨(p.mapPayload_valid_iff _ (fun e => e)).mp h.1,h.2⟩

lemma DefectRouteCertificate.indexedTour_support (c : DefectRouteCertificate s v)
    (p : SegmentRoute V (Fin (2*r))) (hp : p ∈ c.indexedTours)
    (t : Fin (2*r) × Bool) (ht : t ∈ p.tokens) :
    orientedWalkEdge s v t.1 ∈ c.treeEntries := by
  have hmem : p.mapPayload (orientedWalkEdge s v) ∈ expandedDefectRoutes c.segments c.tours := by
    rw [← c.indexedTours_mapPayload]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  exact c.route_entry_support _ hmem _ (List.mem_map.mpr ⟨t,ht,rfl⟩)

lemma DefectRouteCertificate.indexedTour_double (c : DefectRouteCertificate s v)
    (p : SegmentRoute V (Fin (2*r))) (hp : p ∈ c.indexedTours)
    (t : Fin (2*r) × Bool) (ht : t ∈ p.tokens) :
    (p.tokens.map (fun a => orientedWalkEdge s v a.1)).count (orientedWalkEdge s v t.1) = 2 := by
  have hmem : p.mapPayload (orientedWalkEdge s v) ∈ expandedDefectRoutes c.segments c.tours := by
    rw [← c.indexedTours_mapPayload]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have h := c.route_double_entries _ hmem _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  simpa only [SegmentRoute.mapPayload,List.map_map,Function.comp_def,mapSegmentToken] using h

#print axioms DefectRouteCertificate.indexedTours_mapPayload
#print axioms DefectRouteCertificate.indexedTour_valid
#print axioms DefectRouteCertificate.indexedTour_support
#print axioms DefectRouteCertificate.indexedTour_double
end SpectralRadiusUpperTail
