import SpectralRadiusUpperTail.IndexedSegmentCircuits
import SpectralRadiusUpperTail.ExpandedSegmentRoutes

namespace SpectralRadiusUpperTail
variable {σ V : Type*} [DecidableEq V] [DecidableEq σ] [BEq σ] [LawfulBEq σ]

/-- A certificate reorders each original segment exactly once, expands whole
segments (reversing their tokens when required), and preserves primitive labels. -/
lemma reorderSegments_into_closed_routes (ends : σ → V × V) (K : List (SegmentRoute V σ))
    (hK : ∀ p ∈ K, p.Valid ends)
    (hc : ∀ i, Even (((K.flatMap SegmentRoute.tokens).map Prod.fst).count i)) :
    ∃ C : List (SegmentRoute V (Fin K.length)),
      (C.flatMap (fun p => p.tokens.map Prod.fst)).Perm (List.ofFn (fun i : Fin K.length => i)) ∧
      (∀ p ∈ C, p.Valid (fun i => ((K.get i).start,(K.get i).finish)) ∧ p.start = p.finish) ∧
      C.length ≤ K.length ∧
      (∀ p ∈ C.map (expandSegmentRoute (fun i => (K.get i).tokens)),
        p.Valid ends ∧ p.start = p.finish) ∧
      ((C.map (expandSegmentRoute (fun i => (K.get i).tokens))).flatMap
        (fun p => p.tokens.map Prod.fst)).Perm (K.flatMap (fun p => p.tokens.map Prod.fst)) := by
  obtain ⟨C,hC,hlen,hperm⟩ := indexedSegmentCircuits ends K hK hc
  let words : Fin K.length → List (σ × Bool) := fun i => (K.get i).tokens
  let outer : Fin K.length → V × V := fun i => ((K.get i).start,(K.get i).finish)
  have hw : ∀ i, OrientedSegmentChain ends (outer i).1 (outer i).2 (words i) := by
    intro i
    exact (hK (K.get i) (List.get_mem K i)).1
  have hn : ∀ i, words i ≠ [] := by
    intro i
    exact (hK (K.get i) (List.get_mem K i)).2
  refine ⟨C,hperm,hC,hlen,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact ⟨expandSegmentRoute_valid ends outer words hw hn q (hC q hq).1,(hC q hq).2⟩
  · have hm : (((C.map (expandSegmentRoute words)).map SegmentRoute.labels).sum) =
        (K.map SegmentRoute.labels).sum := by
      rw [expandedSegmentCollection_labels]
      let mass : Fin K.length → Multiset σ := fun i => ((words i).map Prod.fst : Multiset σ)
      have hp := (hperm.map mass).sum_eq
      rw [hp]
      have hh := congrArg (List.map SegmentRoute.labels) (List.ofFn_get K)
      have hh' : (List.ofFn (fun i : Fin K.length => i)).map mass = K.map SegmentRoute.labels := by
        simpa only [List.map_ofFn,Function.comp_def,SegmentRoute.labels,words,mass] using hh
      exact congrArg List.sum hh'
    rw [segmentRoute_labels_sum,segmentRoute_labels_sum] at hm
    exact Multiset.coe_eq_coe.mp hm

#print axioms reorderSegments_into_closed_routes
end SpectralRadiusUpperTail
