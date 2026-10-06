import SpectralRadiusUpperTail.ExpandedSegmentRoutes

namespace SpectralRadiusUpperTail
variable {A B I V : Type*}

def mapSegmentToken (f : A → B) (t : A × Bool) : B × Bool := (f t.1,t.2)

lemma mapSegmentToken_reverse (f : A → B) (t : A × Bool) :
    mapSegmentToken f (segmentTokenReverse t) = segmentTokenReverse (mapSegmentToken f t) := rfl

/-- Relabeling primitive payloads commutes with whole-segment reversal,
including the sign flip. Thus original occurrence indices can be propagated
through the existing expansion and relabeled only afterward. -/
lemma expandSegmentToken_map_payload (words : I → List (A × Bool)) (f : A → B)
    (t : I × Bool) :
    (expandSegmentToken words t).map (mapSegmentToken f) =
      expandSegmentToken (fun i => (words i).map (mapSegmentToken f)) t := by
  cases ht : t.2 <;>
    simp [expandSegmentToken,ht,List.map_reverse,List.map_map,Function.comp_def,
      mapSegmentToken,segmentTokenReverse]

lemma expandSegmentRoute_map_payload (words : I → List (A × Bool)) (f : A → B)
    (p : SegmentRoute V I) :
    (expandSegmentRoute words p).tokens.map (mapSegmentToken f) =
      (expandSegmentRoute (fun i => (words i).map (mapSegmentToken f)) p).tokens := by
  simp only [expandSegmentRoute,List.map_flatMap,expandSegmentToken_map_payload]

lemma expandedCollection_map_payload (words : I → List (A × Bool)) (f : A → B)
    (C : List (SegmentRoute V I)) :
    (C.map (fun p => (expandSegmentRoute words p).tokens)).map (List.map (mapSegmentToken f)) =
      C.map (fun p => (expandSegmentRoute (fun i => (words i).map (mapSegmentToken f)) p).tokens) := by
  simp only [List.map_map,Function.comp_def,expandSegmentRoute_map_payload]

#print axioms mapSegmentToken
#print axioms mapSegmentToken_reverse
#print axioms expandSegmentToken_map_payload
#print axioms expandSegmentRoute_map_payload
#print axioms expandedCollection_map_payload
end SpectralRadiusUpperTail
