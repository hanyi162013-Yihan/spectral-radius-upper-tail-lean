import SpectralRadiusUpperTail.SegmentCircuitDecomposition
import SpectralRadiusUpperTail.SegmentCollectionParity
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail
variable {σ V : Type*} [DecidableEq V] [DecidableEq σ] [BEq σ] [LawfulBEq σ]

/-- Reorder indexed whole path segments into closed chains. The permutation of
indices records every input segment exactly once, including equal endpoint pairs. -/
lemma indexedSegmentCircuits (ends : σ → V × V) (K : List (SegmentRoute V σ))
    (hK : ∀ p ∈ K, p.Valid ends)
    (hc : ∀ i, Even (((K.flatMap SegmentRoute.tokens).map Prod.fst).count i)) :
    ∃ C : List (SegmentRoute V (Fin K.length)),
      (∀ p ∈ C, p.Valid (fun i => ((K.get i).start,(K.get i).finish)) ∧
        p.start = p.finish) ∧
      C.length ≤ K.length ∧
      (C.flatMap (fun p => p.tokens.map Prod.fst)).Perm (List.ofFn (fun i : Fin K.length => i)) := by
  have he := segmentCollection_endpoint_even ends K (fun p hp => (hK p hp).1) hc
  let routeEnds : Fin K.length → V × V := fun i => ((K.get i).start,(K.get i).finish)
  have he' : ∀ x, Even (segmentEndpointCount (fun i => (routeEnds i).1)
      (fun i => (routeEnds i).2) (List.ofFn (fun i : Fin K.length => i)) x) := by
    intro x
    have hh := he x
    rw [← List.ofFn_get K] at hh
    simpa only [segmentEndpointCount,List.map_ofFn,Function.comp_def,routeEnds] using hh
  obtain ⟨C,hC,hlen,hperm⟩ := segmentCircuitDecomposition routeEnds
    (List.ofFn (fun i : Fin K.length => i)) he'
  exact ⟨C,hC,by simpa using hlen,hperm⟩

#print axioms indexedSegmentCircuits
end SpectralRadiusUpperTail
