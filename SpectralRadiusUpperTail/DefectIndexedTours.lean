import SpectralRadiusUpperTail.IndexedSegmentPositions
import SpectralRadiusUpperTail.ExpandedOccurrencePermutation
import Mathlib.Data.List.FinRange

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.positionWords (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) : List (Fin (2*r) × Bool) :=
  (c.segmentPositions i).map (fun j => (j,s j))

lemma DefectRouteCertificate.positionWords_payloads (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) :
    (c.positionWords i).map (mapSegmentToken (orientedWalkEdge s v)) = (c.segments.get i).tokens := by
  have h := c.segmentPositions_payloads i
  have ht : c.originalToken = (fun j : Fin (2*r) => (orientedWalkEdge s v j,s j)) := by
    funext j
    rfl
  rw [ht] at h
  simpa only [DefectRouteCertificate.positionWords,List.map_map,Function.comp_def,
    mapSegmentToken] using h

noncomputable def DefectRouteCertificate.indexedTours (c : DefectRouteCertificate s v) :
    List (SegmentRoute V (Fin (2*r))) := c.tours.map (expandSegmentRoute c.positionWords)

/-- The SAME route arrangement carries original step occurrences. Relabeling
them gives the actual expanded certificate, including its reversed signs. -/
lemma DefectRouteCertificate.indexedTours_payloads (c : DefectRouteCertificate s v) :
    (c.indexedTours.map SegmentRoute.tokens).map (List.map (mapSegmentToken (orientedWalkEdge s v))) =
      (expandedDefectRoutes c.segments c.tours).map SegmentRoute.tokens := by
  have h := expandedCollection_map_payload c.positionWords (orientedWalkEdge s v) c.tours
  have hw : (fun i => (c.positionWords i).map (mapSegmentToken (orientedWalkEdge s v))) =
      (fun i => (c.segments.get i).tokens) := funext c.positionWords_payloads
  rw [hw] at h
  simpa only [DefectRouteCertificate.indexedTours,expandedDefectRoutes,List.map_map,
    Function.comp_def] using h

lemma DefectRouteCertificate.indexedTours_positions_perm (c : DefectRouteCertificate s v) :
    (c.indexedTours.flatMap (fun p => p.tokens.map Prod.fst)).Perm c.survivingPositions := by
  have h := expandedOccurrence_ofFn_permutation c.positionWords c.tours c.segment_permutation
  have hw : (fun i => (c.positionWords i).map Prod.fst) = c.segmentPositions := by
    funext i
    simp [DefectRouteCertificate.positionWords,List.map_map,Function.comp_def]
  rw [hw,c.segmentPositions_flatten] at h
  exact h

lemma DefectRouteCertificate.survivingPositions_nodup (c : DefectRouteCertificate s v) :
    c.survivingPositions.Nodup := by
  classical
  exact (List.nodup_ofFn.mpr Function.injective_id).filter _

lemma DefectRouteCertificate.indexedTours_positions_nodup (c : DefectRouteCertificate s v) :
    (c.indexedTours.flatMap (fun p => p.tokens.map Prod.fst)).Nodup :=
  c.indexedTours_positions_perm.nodup_iff.mpr c.survivingPositions_nodup

#print axioms DefectRouteCertificate.positionWords
#print axioms DefectRouteCertificate.positionWords_payloads
#print axioms DefectRouteCertificate.indexedTours
#print axioms DefectRouteCertificate.indexedTours_payloads
#print axioms DefectRouteCertificate.indexedTours_positions_perm
#print axioms DefectRouteCertificate.survivingPositions_nodup
#print axioms DefectRouteCertificate.indexedTours_positions_nodup
end SpectralRadiusUpperTail
