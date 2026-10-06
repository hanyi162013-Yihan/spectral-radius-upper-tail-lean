import SpectralRadiusUpperTail.DefectArrangementLengths
import SpectralRadiusUpperTail.DefectIndexedTours
import SpectralRadiusUpperTail.MarkedChunkCount

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

def DefectRouteCertificate.routeShape (c : DefectRouteCertificate s v) :=
  c.tours.map SegmentRoute.tokens

lemma DefectRouteCertificate.routeShape_nonempty (c : DefectRouteCertificate s v) :
    ∀ l ∈ c.routeShape, l ≠ [] := by
  intro l hl
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hl
  have h := (c.closed_routes (expandSegmentRoute (fun i => (c.segments.get i).tokens) p)
    (List.mem_map.mpr ⟨p,hp,rfl⟩)).1.2
  intro hz
  apply h
  simp only [expandSegmentRoute,hz,List.flatMap_nil]

lemma DefectRouteCertificate.routeShape_total_length (c : DefectRouteCertificate s v) :
    c.routeShape.flatten.length = c.segments.length := by
  have h := c.segment_permutation.length_eq
  simpa only [DefectRouteCertificate.routeShape,List.length_flatten,List.map_map,
    List.length_flatMap,List.length_map,List.length_ofFn,Function.comp_def] using h

/-- The actual position-labelled expanded tours are completely determined by
the deletion set, bounded length array, and small route arrangement. -/
lemma DefectRouteCertificate.decodePositionTours_eq (c : DefectRouteCertificate s v) :
    decodePositionTours s c.deletedPositions c.lengthCode c.routeShape =
      c.indexedTours.map SegmentRoute.tokens := by
  have hw : decodePositionWord s c.deletedPositions c.lengthCode = c.positionWords :=
    funext c.decodePositionWord_eq
  simp only [decodePositionTours,hw,DefectRouteCertificate.routeShape,
    DefectRouteCertificate.indexedTours,List.map_map,Function.comp_def,expandSegmentRoute]

lemma DefectRouteCertificate.segment_count_le_length (c : DefectRouteCertificate s v) :
    c.segments.length ≤ 2*r := by
  have hsum : (∑ i : Fin c.segments.length, (c.segmentPositions i).length) =
      c.survivingPositions.length := by
    have h := congrArg List.length c.segmentPositions_flatten
    simpa only [List.length_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def] using h
  calc
    c.segments.length = ∑ _i : Fin c.segments.length, 1 := by simp
    _ ≤ ∑ i : Fin c.segments.length, (c.segmentPositions i).length :=
      Finset.sum_le_sum (fun i _ => Nat.succ_le_of_lt
        (List.length_pos_iff.mpr (c.segmentPositions_nonempty i)))
    _ = c.survivingPositions.length := hsum
    _ ≤ 2*r := c.survivingPositions_length_le

def DefectRouteCertificate.arrangementShapeCode (c : DefectRouteCertificate s v) :
    {C : List (List (Fin c.segments.length × Bool)) //
      (∀ l ∈ C, l ≠ []) ∧ C.flatten.length = c.segments.length} :=
  ⟨c.routeShape,c.routeShape_nonempty,c.routeShape_total_length⟩

#print axioms DefectRouteCertificate.routeShape
#print axioms DefectRouteCertificate.routeShape_nonempty
#print axioms DefectRouteCertificate.routeShape_total_length
#print axioms DefectRouteCertificate.decodePositionTours_eq
#print axioms DefectRouteCertificate.segment_count_le_length
#print axioms DefectRouteCertificate.arrangementShapeCode
end SpectralRadiusUpperTail
