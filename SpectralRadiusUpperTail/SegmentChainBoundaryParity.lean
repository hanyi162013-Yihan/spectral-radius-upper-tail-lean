import SpectralRadiusUpperTail.OrientedSegmentChain
import SpectralRadiusUpperTail.SegmentEndpointParity

namespace SpectralRadiusUpperTail
variable {σ V : Type*} [DecidableEq V]

/-- Internal visits contribute twice. The parity of all primitive segment
incidences agrees with the parity of the two outer endpoints of a chain. -/
lemma OrientedSegmentChain.boundary_even {ends : σ → V × V} {a b : V}
    {L : List (σ × Bool)} (h : OrientedSegmentChain ends a b L) (x : V) :
    Even (segmentEndpointCount (segmentTokenStart ends) (segmentTokenFinish ends) L x +
      (if a = x then 1 else 0) + (if b = x then 1 else 0)) := by
  induction h with
  | nil a =>
    refine ⟨if a = x then 1 else 0,?_⟩
    simp [segmentEndpointCount]
  | cons t h ih =>
    obtain ⟨k,hk⟩ := ih
    refine ⟨k + (if segmentTokenStart ends t = x then 1 else 0),?_⟩
    rw [segmentEndpointCount_cons]
    omega

/-- Orientation of a primitive segment does not affect its endpoint incidence. -/
lemma segmentToken_endpoint_count (ends : σ → V × V) (L : List (σ × Bool)) (x : V) :
    segmentEndpointCount (segmentTokenStart ends) (segmentTokenFinish ends) L x =
      segmentEndpointCount (fun i => (ends i).1) (fun i => (ends i).2)
        (L.map Prod.fst) x := by
  unfold segmentEndpointCount
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  cases ht : t.2 <;>
    simp [segmentTokenStart,segmentTokenFinish,ht,Nat.add_comm]

#print axioms OrientedSegmentChain.boundary_even
#print axioms segmentToken_endpoint_count
end SpectralRadiusUpperTail
