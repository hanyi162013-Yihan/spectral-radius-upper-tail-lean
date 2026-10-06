import SpectralRadiusUpperTail.SegmentRoute
import SpectralRadiusUpperTail.SegmentCutCrossingParity
import SpectralRadiusUpperTail.BridgeCutStep
import SpectralRadiusUpperTail.OrientedEdgeSymmetry
import SpectralRadiusUpperTail.FiniteWordListCount

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a consistently oriented tree support, crossing an edge's bridge cut is
exactly the event that the primitive directed entry is that edge. -/
lemma treeSegment_cut_iff_entry (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (e : V × V) (he : e ∈ T) (t : (V × V) × Bool) (htok : t.1 ∈ T) :
    bridgeCutColor (walkSupportGraph T) e.1 e.2 (segmentTokenStart (fun x => x) t) ≠
      bridgeCutColor (walkSupportGraph T) e.1 e.2 (segmentTokenFinish (fun x => x) t) ↔ t.1 = e := by
  have hloop : ∀ a b, (a,b) ∈ T → a ≠ b := by
    intro a b hab hh
    subst b
    exact hno a a hab hab
  have hea : (walkSupportGraph T).Adj e.1 e.2 := ⟨hloop _ _ he,Or.inl he⟩
  have hta : (walkSupportGraph T).Adj t.1.1 t.1.2 := ⟨hloop _ _ htok,Or.inl htok⟩
  have hb := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic hea
  have hc := not_congr (bridgeCutColor_same_iff_other_edge (walkSupportGraph T)
    e.1 e.2 t.1.1 t.1.2 hb hta)
  have hi : s(t.1.1,t.1.2) = s(e.1,e.2) ↔ t.1 = e := by
    exact ⟨fun h => orientedEdgeSet_sym2_injective T hno htok he h,
      fun h => congrArg (fun x : V × V => s(x.1,x.2)) h⟩
  have hc' : bridgeCutColor (walkSupportGraph T) e.1 e.2 t.1.1 ≠
      bridgeCutColor (walkSupportGraph T) e.1 e.2 t.1.2 ↔ t.1 = e := by
    simpa only [not_not,hi] using hc
  cases hs : t.2
  · simpa [segmentTokenStart,segmentTokenFinish,hs] using hc'
  · simpa [segmentTokenStart,segmentTokenFinish,hs,ne_comm] using hc'

/-- Every primitive entry appears an even number of times in a closed route
whose support is contained in an oriented tree. -/
lemma closedTreeRoute_entry_even (T : Finset (V × V))
    (ht : (walkSupportGraph T).IsTree)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (p : SegmentRoute V (V × V))
    (hp : OrientedSegmentChain (fun e => e) p.start p.finish p.tokens)
    (hclosed : p.start = p.finish) (hT : ∀ t ∈ p.tokens, t.1 ∈ T) (e : V × V) :
    Even ((p.tokens.map Prod.fst).count e) := by
  by_cases he : e ∈ T
  · let color := bridgeCutColor (walkSupportGraph T) e.1 e.2
    have hc := (hclosed ▸ hp).closed_cut_crossing_even color
    have hcount : (p.tokens.map Prod.fst).count e =
        (p.tokens.filter (fun t => decide
          (color (segmentTokenStart (fun x => x) t) ≠ color (segmentTokenFinish (fun x => x) t)))).length := by
      rw [list_count_indicator_sum,list_filter_length_indicator,List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht'
      have hh := treeSegment_cut_iff_entry T ht hno e he t (hT t ht')
      simp only [Function.comp_def,decide_eq_true_eq,color,hh]
    rw [hcount]
    exact hc
  · have hz : (p.tokens.map Prod.fst).count e = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      obtain ⟨t,ht',heq⟩ := List.mem_map.mp hm
      exact he (heq ▸ hT t ht')
    rw [hz]
    exact ⟨0,rfl⟩

#print axioms treeSegment_cut_iff_entry
#print axioms closedTreeRoute_entry_even
end SpectralRadiusUpperTail
