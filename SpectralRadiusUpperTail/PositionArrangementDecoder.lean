import SpectralRadiusUpperTail.PartitionByLengths
import SpectralRadiusUpperTail.SegmentPayloadTransport
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail

/-- Chronological retained positions, determined by the deletion set alone. -/
def retainedPositionList {L : ℕ} (D : Finset (Fin L)) : List (Fin L) :=
  (List.ofFn (fun i : Fin L => i)).filter (fun i => decide (i ∉ D))

/-- All primitive position words are decoded from bounded segment lengths.
No original matrix-entry or vertex labels are present. -/
def decodePositionWord {L S : ℕ} (s : Fin L → Bool) (D : Finset (Fin L))
    (lengths : Fin S → Fin (L+1)) (i : Fin S) : List (Fin L × Bool) :=
  ((partitionByLengths (List.ofFn (fun j => (lengths j).val))
    (retainedPositionList D)).getD i.val []).map (fun j => (j,s j))

def decodePositionTours {L S : ℕ} (s : Fin L → Bool) (D : Finset (Fin L))
    (lengths : Fin S → Fin (L+1)) (routes : List (List (Fin S × Bool))) :
    List (List (Fin L × Bool)) :=
  routes.map (fun toks => toks.flatMap (expandSegmentToken (decodePositionWord s D lengths)))

/-- This equality makes the dependence on the small shape records explicit. -/
lemma decodePositionTours_congr {L S : ℕ} (s : Fin L → Bool)
    {D E : Finset (Fin L)} {l k : Fin S → Fin (L+1)}
    {C K : List (List (Fin S × Bool))} (hD : D = E) (hl : l = k) (hC : C = K) :
    decodePositionTours s D l C = decodePositionTours s E k K := by
  cases hD
  cases hl
  cases hC
  rfl

#print axioms retainedPositionList
#print axioms decodePositionWord
#print axioms decodePositionTours
#print axioms decodePositionTours_congr
end SpectralRadiusUpperTail
