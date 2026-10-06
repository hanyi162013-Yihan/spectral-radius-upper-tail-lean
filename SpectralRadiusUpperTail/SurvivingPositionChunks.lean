import SpectralRadiusUpperTail.PartitionByLengths
import SpectralRadiusUpperTail.RetainedPositionExtension

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

def DefectRouteCertificate.originalToken (_c : DefectRouteCertificate s v) (i : Fin (2*r)) :=
  (orientedWalkEdge s v i,s i)

noncomputable def DefectRouteCertificate.survivingPositions (c : DefectRouteCertificate s v) :
    List (Fin (2*r)) :=
  (List.ofFn (fun i : Fin (2*r) => i)).filter (fun i => decide
    (orientedWalkEdge s v i ∈ c.treeEntries ∧
      entryMultiplicity (orientedWalkEdge s v) (orientedWalkEdge s v i) = 2))

lemma DefectRouteCertificate.survivingPositions_tokens (c : DefectRouteCertificate s v) :
    c.survivingPositions.map c.originalToken = c.segments.flatMap SegmentRoute.tokens := by
  classical
  rw [c.surviving_order]
  have htoken : c.originalToken = (fun i : Fin (2*r) => (orientedWalkEdge s v i,s i)) := by
    funext i
    rfl
  rw [htoken]
  dsimp only [DefectRouteCertificate.survivingPositions,DefectRouteCertificate.originalToken]
  simpa only [List.map_ofFn,Function.comp_def] using
    (List.filter_map
      (f := fun i : Fin (2*r) => (orientedWalkEdge s v i,s i))
      (p := fun t : (V × V) × Bool => decide
        (t.1 ∈ c.treeEntries ∧ entryMultiplicity (orientedWalkEdge s v) t.1 = 2))
      (l := List.ofFn (fun i : Fin (2*r) => i))).symm

lemma DefectRouteCertificate.mem_survivingPositions (c : DefectRouteCertificate s v)
    (i : Fin (2*r)) : i ∈ c.survivingPositions ↔ i ∉ c.deletedPositions := by
  classical
  simp [DefectRouteCertificate.survivingPositions,DefectRouteCertificate.deletedPositions,
    not_or,and_comm]

noncomputable def DefectRouteCertificate.segmentPositionChunks (c : DefectRouteCertificate s v) :=
  partitionByLengths (c.segments.map (fun p => p.tokens.length)) c.survivingPositions

/-- Original indices are assigned to segments only through deletion and length
records. Mapping their payloads gives exactly the actual certificate segments. -/
lemma DefectRouteCertificate.segmentPositionChunks_payloads (c : DefectRouteCertificate s v) :
    c.segmentPositionChunks.map (List.map c.originalToken) = c.segments.map SegmentRoute.tokens := by
  have h := partitionByLengths_map_eq c.survivingPositions c.originalToken
    (c.segments.map SegmentRoute.tokens) (by
      simpa only [List.flatMap_def] using c.survivingPositions_tokens)
  simpa only [DefectRouteCertificate.segmentPositionChunks,List.map_map,Function.comp_def] using h

lemma DefectRouteCertificate.segment_lengths_sum (c : DefectRouteCertificate s v) :
    (c.segments.map (fun p => p.tokens.length)).sum = c.survivingPositions.length := by
  have h := congrArg List.length c.survivingPositions_tokens
  simpa only [List.length_map,List.length_flatMap] using h.symm

lemma DefectRouteCertificate.segmentPositionChunks_lengths (c : DefectRouteCertificate s v) :
    c.segmentPositionChunks.map List.length = c.segments.map (fun p => p.tokens.length) :=
  partitionByLengths_lengths _ _ c.segment_lengths_sum

lemma DefectRouteCertificate.segmentPositionChunks_flatten (c : DefectRouteCertificate s v) :
    c.segmentPositionChunks.flatten = c.survivingPositions :=
  partitionByLengths_flatten _ _ c.segment_lengths_sum

lemma DefectRouteCertificate.segmentPositionChunks_length (c : DefectRouteCertificate s v) :
    c.segmentPositionChunks.length = c.segments.length := by
  simp only [DefectRouteCertificate.segmentPositionChunks,partitionByLengths_length,List.length_map]

#print axioms DefectRouteCertificate.originalToken
#print axioms DefectRouteCertificate.survivingPositions
#print axioms DefectRouteCertificate.survivingPositions_tokens
#print axioms DefectRouteCertificate.mem_survivingPositions
#print axioms DefectRouteCertificate.segmentPositionChunks
#print axioms DefectRouteCertificate.segmentPositionChunks_payloads
#print axioms DefectRouteCertificate.segment_lengths_sum
#print axioms DefectRouteCertificate.segmentPositionChunks_lengths
#print axioms DefectRouteCertificate.segmentPositionChunks_flatten
#print axioms DefectRouteCertificate.segmentPositionChunks_length
end SpectralRadiusUpperTail
