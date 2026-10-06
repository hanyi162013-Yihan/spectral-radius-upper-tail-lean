import SpectralRadiusUpperTail.SegmentChainSubstitution
import SpectralRadiusUpperTail.SegmentCircuitDecomposition

namespace SpectralRadiusUpperTail
variable {σ τ V : Type*}

def expandSegmentRoute (words : τ → List (σ × Bool)) (p : SegmentRoute V τ) : SegmentRoute V σ :=
  ⟨p.start,p.finish,p.tokens.flatMap (expandSegmentToken words)⟩

lemma expandSegmentRoute_valid (ends : σ → V × V) (outer : τ → V × V)
    (words : τ → List (σ × Bool))
    (hc : ∀ i, OrientedSegmentChain ends (outer i).1 (outer i).2 (words i))
    (hn : ∀ i, words i ≠ []) (p : SegmentRoute V τ) (hp : p.Valid outer) :
    (expandSegmentRoute words p).Valid ends :=
  ⟨hp.1.substitute words hc,expandedSegmentRoute_nonempty words hn p.tokens hp.2⟩

lemma expandSegmentToken_labels (words : τ → List (σ × Bool)) (t : τ × Bool) :
    (((expandSegmentToken words t).map Prod.fst : List σ) : Multiset σ) =
      ((words t.1).map Prod.fst : List σ) := by
  cases ht : t.2 <;>
    simp [expandSegmentToken,ht,List.map_reverse,List.map_map,segmentTokenReverse,Function.comp_def]

lemma expandSegmentRoute_labels (words : τ → List (σ × Bool)) (p : SegmentRoute V τ) :
    (expandSegmentRoute words p).labels =
      ((p.tokens.map Prod.fst).map (fun i => ((words i).map Prod.fst : Multiset σ))).sum := by
  change (((p.tokens.flatMap (expandSegmentToken words)).map Prod.fst : List σ) : Multiset σ) = _
  generalize p.tokens = L
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons,List.sum_cons]
    rw [← Multiset.coe_add,expandSegmentToken_labels,ih]

lemma expandedSegmentCollection_labels (words : τ → List (σ × Bool))
    (C : List (SegmentRoute V τ)) :
    ((C.map (expandSegmentRoute words)).map SegmentRoute.labels).sum =
      ((C.flatMap (fun p => p.tokens.map Prod.fst)).map
        (fun i => ((words i).map Prod.fst : Multiset σ))).sum := by
  induction C with
  | nil => simp
  | cons p C ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append]
    rw [expandSegmentRoute_labels,ih]

#print axioms expandSegmentRoute
#print axioms expandSegmentRoute_valid
#print axioms expandSegmentToken_labels
#print axioms expandSegmentRoute_labels
#print axioms expandedSegmentCollection_labels
end SpectralRadiusUpperTail
