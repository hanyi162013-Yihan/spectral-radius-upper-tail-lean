import SpectralRadiusUpperTail.DefectArrangementShape

namespace SpectralRadiusUpperTail

/-- Economical shape data. S segment lengths and S signed segment occurrences
are recorded; primitive occurrence lists are decoded, not freely stored. -/
structure PositionArrangementCode (L S : ℕ) where
  deleted : Finset (Fin L)
  lengths : Fin S → Fin (L+1)
  routes : List (List (Fin S × Bool))
  nonempty : ∀ l ∈ routes, l ≠ []
  total : routes.flatten.length = S

def PositionArrangementCode.decode {L S : ℕ} (s : Fin L → Bool)
    (C : PositionArrangementCode L S) := decodePositionTours s C.deleted C.lengths C.routes

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.positionArrangementCode (c : DefectRouteCertificate s v) :
    PositionArrangementCode (2*r) c.segments.length :=
  ⟨c.deletedPositions,c.lengthCode,c.routeShape,c.routeShape_nonempty,c.routeShape_total_length⟩

lemma DefectRouteCertificate.positionArrangementCode_decode (c : DefectRouteCertificate s v) :
    c.positionArrangementCode.decode s = c.indexedTours.map SegmentRoute.tokens :=
  c.decodePositionTours_eq

#print axioms PositionArrangementCode
#print axioms PositionArrangementCode.decode
#print axioms DefectRouteCertificate.positionArrangementCode
#print axioms DefectRouteCertificate.positionArrangementCode_decode
end SpectralRadiusUpperTail
