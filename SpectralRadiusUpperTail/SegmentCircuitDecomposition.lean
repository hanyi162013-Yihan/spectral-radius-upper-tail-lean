import SpectralRadiusUpperTail.SegmentClosedAssembly
import SpectralRadiusUpperTail.SegmentRoute

namespace SpectralRadiusUpperTail
variable {σ V : Type*} [DecidableEq V]

lemma segmentRoute_labels_sum (K : List (SegmentRoute V σ)) :
    (K.map SegmentRoute.labels).sum =
      ((K.flatMap (fun p => p.tokens.map Prod.fst) : List σ) : Multiset σ) := by
  induction K with
  | nil => simp
  | cons p K ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,ih]
    exact Multiset.coe_add _ _

/-- Finite segments with even endpoint incidences admit a decomposition into
nonempty closed chains. Every original segment label occurs with exactly its
original multiplicity; arbitrary parallel segments and loops are permitted. -/
lemma segmentCircuitDecomposition (ends : σ → V × V) (L : List σ)
    (heven : ∀ x, Even (segmentEndpointCount (fun i => (ends i).1)
      (fun i => (ends i).2) L x)) :
    ∃ K : List (SegmentRoute V σ),
      (∀ p ∈ K, p.Valid ends ∧ p.start = p.finish) ∧
      K.length ≤ L.length ∧
      (K.flatMap (fun p => p.tokens.map Prod.fst)).Perm L := by
  let initial := L.map (SegmentRoute.single ends)
  have hv : ∀ p ∈ initial, p.Valid ends := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact SegmentRoute.single_valid ends i
  have he : ∀ x, Even (segmentEndpointCount SegmentRoute.start SegmentRoute.finish initial x) := by
    intro x
    dsimp only [initial,segmentEndpointCount]
    rw [List.map_map]
    exact heven x
  obtain ⟨K,hK,hlen,hmass⟩ := segmentClosedAssembly SegmentRoute.start SegmentRoute.finish
    SegmentRoute.reverse SegmentRoute.join SegmentRoute.labels (SegmentRoute.Valid ends)
    (fun _ => rfl) (fun _ => rfl) SegmentRoute.reverse_labels
    (SegmentRoute.reverse_valid ends) (fun _ _ => rfl) (fun _ _ => rfl)
    SegmentRoute.join_labels (SegmentRoute.join_valid ends) initial hv he
  refine ⟨K,hK,?_,?_⟩
  · simpa [initial] using hlen
  · apply Multiset.coe_eq_coe.mp
    rw [← segmentRoute_labels_sum,hmass,segmentRoute_labels_sum]
    simp [initial,List.flatMap_map,SegmentRoute.single,Function.comp_def]

#print axioms segmentRoute_labels_sum
#print axioms segmentCircuitDecomposition
end SpectralRadiusUpperTail
