import SpectralRadiusUpperTail.SegmentPayloadTransport

namespace SpectralRadiusUpperTail
variable {A I : Type*}

def reverseTokenFragment (w : List (A × Bool)) := w.reverse.map segmentTokenReverse

/-- Reverse the order of fragments AND reverse/flip each fragment, retaining
all original fragment boundaries. -/
def expandFragmentToken (P : I → List (List (A × Bool))) (t : I × Bool) :
    List (List (A × Bool)) :=
  if t.2 then (P t.1).reverse.map reverseTokenFragment else P t.1

lemma expandFragmentToken_flatten (P : I → List (List (A × Bool))) (t : I × Bool) :
    (expandFragmentToken P t).flatten = expandSegmentToken (fun i => (P i).flatten) t := by
  cases ht : t.2
  · simp [expandFragmentToken,expandSegmentToken,ht]
  · simp only [expandFragmentToken,expandSegmentToken,ht,if_true,reverseTokenFragment,
      List.reverse_flatten,List.map_flatten,List.map_reverse,List.map_map,Function.comp_def]
    have hf : @reverseTokenFragment A =
        (fun w : List (A × Bool) => (w.map segmentTokenReverse).reverse) := by
      funext w
      exact List.map_reverse
    rw [hf]

lemma expandFragmentToken_length (P : I → List (List (A × Bool))) (t : I × Bool) :
    (expandFragmentToken P t).length = (P t.1).length := by
  cases ht : t.2 <;> simp [expandFragmentToken,ht]

lemma expandFragmentRoute_flatten (P : I → List (List (A × Bool))) (toks : List (I × Bool)) :
    (toks.flatMap (expandFragmentToken P)).flatten =
      toks.flatMap (expandSegmentToken (fun i => (P i).flatten)) := by
  induction toks with
  | nil => rfl
  | cons t toks ih =>
    simp only [List.flatMap_cons,List.flatten_append,expandFragmentToken_flatten,ih]

#print axioms reverseTokenFragment
#print axioms expandFragmentToken
#print axioms expandFragmentToken_flatten
#print axioms expandFragmentToken_length
#print axioms expandFragmentRoute_flatten
end SpectralRadiusUpperTail
