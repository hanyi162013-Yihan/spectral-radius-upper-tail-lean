import SpectralRadiusUpperTail.ListTourMatchingBound
import SpectralRadiusUpperTail.TokenSignMatchingTransport

namespace SpectralRadiusUpperTail
variable {A : Type*}

lemma tokenTour_fragment_matching_count_le (W P : List (List (A × Bool)))
    (hflat : P.flatten = W.flatten) (hconst : ∀ p ∈ P, labelConstant Prod.snd p)
    (m L B K : ℕ) (hmL : m ≤ L) (hlen : ∀ p ∈ P, p.length ≤ m)
    (hnum : P.length ≤ B+K) :
    (W.map (fun w => Nat.card (SignedNoncrossingMatching
      (fun i : Fin w.length => (w.get i).2)))).prod ≤ (m+1)^B * (L+1)^K := by
  let WS := W.map (List.map Prod.snd)
  let PS := P.map (List.map Prod.snd)
  have hf : PS.flatten = WS.flatten := by
    change (P.map (List.map Prod.snd)).flatten = (W.map (List.map Prod.snd)).flatten
    rw [← List.map_flatten,← List.map_flatten,hflat]
  have hc : ∀ p ∈ PS, labelConstant id p := by
    intro p hp
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hp
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    exact hconst w hw x hx y hy
  have hl : ∀ p ∈ PS, p.length ≤ m := by
    intro p hp
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hp
    simpa only [List.length_map] using hlen w hw
  have hn : PS.length ≤ B+K := by simpa only [PS,List.length_map] using hnum
  have h := listTour_fragment_matching_count_le WS PS hf hc m L B K hmL hl hn
  simp only [WS,List.map_map,Function.comp_def] at h
  simpa only [tokenSignMatching_card] using h

#print axioms tokenTour_fragment_matching_count_le
end SpectralRadiusUpperTail
