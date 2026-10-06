import SpectralRadiusUpperTail.SegmentChainPayload

namespace SpectralRadiusUpperTail
variable {A B V : Type*}

def SegmentRoute.mapPayload (f : A → B) (p : SegmentRoute V A) : SegmentRoute V B :=
  ⟨p.start,p.finish,p.tokens.map (mapSegmentToken f)⟩

lemma SegmentRoute.mapPayload_valid_iff (f : A → B) (ends : B → V × V)
    (p : SegmentRoute V A) :
    (p.mapPayload f).Valid ends ↔ p.Valid (ends ∘ f) := by
  simp only [SegmentRoute.Valid,SegmentRoute.mapPayload,segmentChain_map_payload_iff,
    ne_eq,List.map_eq_nil_iff]

lemma expandSegmentRoute_mapPayload (f : A → B) {I : Type*}
    (words : I → List (A × Bool)) (p : SegmentRoute V I) :
    (expandSegmentRoute words p).mapPayload f =
      expandSegmentRoute (fun i => (words i).map (mapSegmentToken f)) p := by
  have h := expandSegmentRoute_map_payload words f p
  cases p
  simp only [SegmentRoute.mapPayload,expandSegmentRoute] at h ⊢
  exact congrArg (fun t => SegmentRoute.mk _ _ t) h

#print axioms SegmentRoute.mapPayload
#print axioms SegmentRoute.mapPayload_valid_iff
#print axioms expandSegmentRoute_mapPayload
end SpectralRadiusUpperTail
