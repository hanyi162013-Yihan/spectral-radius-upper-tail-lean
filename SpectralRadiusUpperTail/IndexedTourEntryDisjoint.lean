import SpectralRadiusUpperTail.IndexedTourPath
import SpectralRadiusUpperTail.DoubleCountDisjoint

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.indexedTours_entry_count (c : DefectRouteCertificate s v)
    (e : V × V) :
    (∑ i : Fin c.indexedTours.length,
      (((c.indexedTours.get i).tokens).map (fun t => orientedWalkEdge s v t.1)).count e) ≤ 2 := by
  let Q := c.indexedTours
  let F := fun p : SegmentRoute V (Fin (2*r)) =>
    (p.tokens.map (fun t => orientedWalkEdge s v t.1)).count e
  have hh := congrArg (fun J : List (SegmentRoute V (Fin (2*r))) => (J.map F).sum)
    (List.ofFn_get Q)
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def] at hh
  change (∑ i : Fin Q.length, F (Q.get i)) ≤ 2
  rw [hh]
  have hflat : Q.flatMap (fun p => p.tokens.map (fun t => orientedWalkEdge s v t.1)) =
      (expandedDefectRoutes c.segments c.tours).flatMap (fun p => p.tokens.map Prod.fst) := by
    rw [← c.indexedTours_mapPayload]
    simp only [List.flatMap_map,SegmentRoute.mapPayload,List.map_map,Function.comp_def,mapSegmentToken,Q]
  have hcount := congrArg (fun L : List (V × V) => L.count e) hflat
  rw [List.count_flatMap] at hcount
  change (Q.map F).sum = _ at hcount
  rw [hcount,c.total_entry_counts]
  split_ifs <;> omega

lemma DefectRouteCertificate.indexedPath_entries_disjoint (c : DefectRouteCertificate s v) :
    Pairwise (fun i j => Disjoint
      (Finset.univ.image (orientedWalkEdge (c.indexedSigns i) (c.indexedPath i).vertices))
      (Finset.univ.image (orientedWalkEdge (c.indexedSigns j) (c.indexedPath j).vertices))) := by
  apply doubleCount_supports_disjoint
    (fun i : Fin c.indexedTours.length =>
      (c.indexedTours.get i).tokens.map (fun t => orientedWalkEdge s v t.1))
  · intro i e he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
    have heq := (c.indexedPath i).entries j
    change orientedWalkEdge (c.indexedSigns i) (c.indexedPath i).vertices j = _ at heq
    rw [heq]
    exact c.indexedTour_double _ (List.get_mem _ i) _ (List.get_mem _ j)
  · exact c.indexedTours_entry_count

#print axioms DefectRouteCertificate.indexedTours_entry_count
#print axioms DefectRouteCertificate.indexedPath_entries_disjoint
end SpectralRadiusUpperTail
