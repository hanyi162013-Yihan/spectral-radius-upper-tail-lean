import SpectralRadiusUpperTail.SegmentRoute

namespace SpectralRadiusUpperTail
variable {σ τ V : Type*}

/-- Expand an oriented named segment into all of its primitive tokens. -/
def expandSegmentToken (words : τ → List (σ × Bool)) (t : τ × Bool) : List (σ × Bool) :=
  if t.2 then (words t.1).reverse.map segmentTokenReverse else words t.1

lemma expandSegmentToken_nonempty (words : τ → List (σ × Bool))
    (hw : ∀ i, words i ≠ []) (t : τ × Bool) : expandSegmentToken words t ≠ [] := by
  cases ht : t.2 <;> simpa [expandSegmentToken,ht] using hw t.1

lemma expandSegmentToken_chain (ends : σ → V × V) (outer : τ → V × V)
    (words : τ → List (σ × Bool))
    (hw : ∀ i, OrientedSegmentChain ends (outer i).1 (outer i).2 (words i))
    (t : τ × Bool) :
    OrientedSegmentChain ends (segmentTokenStart outer t) (segmentTokenFinish outer t)
      (expandSegmentToken words t) := by
  cases ht : t.2
  · simpa [expandSegmentToken,segmentTokenStart,segmentTokenFinish,ht] using hw t.1
  · simpa [expandSegmentToken,segmentTokenStart,segmentTokenFinish,ht] using (hw t.1).reverse

/-- Substituting entire valid chains preserves all endpoint joins, including
when a named chain is reversed. -/
lemma OrientedSegmentChain.substitute {ends : σ → V × V} {outer : τ → V × V}
    {a b : V} {L : List (τ × Bool)} (h : OrientedSegmentChain outer a b L)
    (words : τ → List (σ × Bool))
    (hw : ∀ i, OrientedSegmentChain ends (outer i).1 (outer i).2 (words i)) :
    OrientedSegmentChain ends a b (L.flatMap (expandSegmentToken words)) := by
  induction h with
  | nil a => exact .nil a
  | cons t h ih =>
    exact (expandSegmentToken_chain ends outer words hw t).append ih

lemma expandedSegmentRoute_nonempty (words : τ → List (σ × Bool))
    (hw : ∀ i, words i ≠ []) (L : List (τ × Bool)) (hL : L ≠ []) :
    L.flatMap (expandSegmentToken words) ≠ [] := by
  cases L with
  | nil => exact False.elim (hL rfl)
  | cons t L =>
    intro hz
    have hh : expandSegmentToken words t = [] := (List.append_eq_nil_iff.mp hz).1
    exact expandSegmentToken_nonempty words hw t hh

#print axioms expandSegmentToken
#print axioms expandSegmentToken_nonempty
#print axioms expandSegmentToken_chain
#print axioms OrientedSegmentChain.substitute
#print axioms expandedSegmentRoute_nonempty
end SpectralRadiusUpperTail
