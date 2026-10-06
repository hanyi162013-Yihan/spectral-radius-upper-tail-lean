import SpectralRadiusUpperTail.ListSignMatchingTransport
import SpectralRadiusUpperTail.ChunkMatchingBound

namespace SpectralRadiusUpperTail

lemma listTour_matching_count_le_flat (W : List (List Bool)) :
    (W.map (fun w => Nat.card (SignedNoncrossingMatching
      (fun i : Fin w.length => w.get i)))).prod ≤
    Nat.card (SignedNoncrossingMatching (fun i : Fin W.flatten.length => W.flatten.get i)) := by
  let F : List FiniteSignWord := W.map (fun w => ⟨w.length,w.get⟩)
  have h := concatenateSignedMatchings_count_le F
  rw [concatenateSigns_listMatchingCard] at h
  have hf : F.flatMap (fun w => List.ofFn w.2) = W.flatten := by
    simp only [F,List.flatMap_map,List.ofFn_get]
    exact List.flatMap_id
  rw [hf] at h
  simpa only [F,List.map_map,Function.comp_def] using h

/-- Only the actual total fragment count and fragment lengths enter the bound;
no product of independent vertex-pattern counts is used. -/
lemma listTour_fragment_matching_count_le (W P : List (List Bool))
    (hflat : P.flatten = W.flatten) (hconst : ∀ p ∈ P, labelConstant id p)
    (m L B K : ℕ) (hmL : m ≤ L) (hlen : ∀ p ∈ P, p.length ≤ m)
    (hnum : P.length ≤ B+K) :
    (W.map (fun w => Nat.card (SignedNoncrossingMatching
      (fun i : Fin w.length => w.get i)))).prod ≤ (m+1)^B * (L+1)^K := by
  have h := chunk_matching_count_le P hconst m L B K hmL hlen hnum
  rw [hflat] at h
  exact (listTour_matching_count_le_flat W).trans h

#print axioms listTour_matching_count_le_flat
#print axioms listTour_fragment_matching_count_le
end SpectralRadiusUpperTail
