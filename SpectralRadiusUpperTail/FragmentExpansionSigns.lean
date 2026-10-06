import SpectralRadiusUpperTail.FragmentExpansion
import SpectralRadiusUpperTail.ConstantRunPartition

namespace SpectralRadiusUpperTail
variable {A I : Type*}

lemma reverseTokenFragment_properties (w : List (A × Bool))
    (hne : w ≠ []) (hconst : labelConstant Prod.snd w) (m : ℕ) (hlen : w.length ≤ m) :
    reverseTokenFragment w ≠ [] ∧ labelConstant Prod.snd (reverseTokenFragment w) ∧
      (reverseTokenFragment w).length ≤ m := by
  refine ⟨by simpa [reverseTokenFragment] using hne,?_,by simpa [reverseTokenFragment] using hlen⟩
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  exact congrArg Bool.not (hconst a (List.mem_reverse.mp ha) b (List.mem_reverse.mp hb))

lemma expandFragmentToken_properties (P : I → List (List (A × Bool))) (m : ℕ)
    (hP : ∀ i w, w ∈ P i → w ≠ [] ∧ labelConstant Prod.snd w ∧ w.length ≤ m)
    (t : I × Bool) (w : List (A × Bool)) (hw : w ∈ expandFragmentToken P t) :
    w ≠ [] ∧ labelConstant Prod.snd w ∧ w.length ≤ m := by
  cases ht : t.2
  · simp only [expandFragmentToken,ht,Bool.false_eq_true,if_false] at hw
    exact hP t.1 w hw
  · simp only [expandFragmentToken,ht,if_true] at hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    have h := hP t.1 a (List.mem_reverse.mp ha)
    exact reverseTokenFragment_properties a h.1 h.2.1 m h.2.2

lemma expandFragmentRoute_properties (P : I → List (List (A × Bool))) (m : ℕ)
    (hP : ∀ i w, w ∈ P i → w ≠ [] ∧ labelConstant Prod.snd w ∧ w.length ≤ m)
    (toks : List (I × Bool)) (w : List (A × Bool)) (hw : w ∈ toks.flatMap (expandFragmentToken P)) :
    w ≠ [] ∧ labelConstant Prod.snd w ∧ w.length ≤ m := by
  obtain ⟨t,_,ht⟩ := List.mem_flatMap.mp hw
  exact expandFragmentToken_properties P m hP t w ht

#print axioms reverseTokenFragment_properties
#print axioms expandFragmentToken_properties
#print axioms expandFragmentRoute_properties
end SpectralRadiusUpperTail
