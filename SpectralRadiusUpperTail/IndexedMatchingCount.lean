import SpectralRadiusUpperTail.IndexedTourFragments
import SpectralRadiusUpperTail.TokenTourMatchingBound
import SpectralRadiusUpperTail.IndexedTourPath
import SpectralRadiusUpperTail.OccurrenceFamily

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.indexedMatching_count_le (c : DefectRouteCertificate s v)
    (block : Fin (2*r) → B) (N m : ℕ)
    (hrun : signRunCount (List.ofFn block) ≤ N)
    (hcount : ∀ b, (List.ofFn block).count b ≤ m)
    (hsign : ∀ i j, block i = block j → s i = s j) (hm : m ≤ 2*r) :
    Nat.card (∀ i : Fin c.indexedTours.length, SignedNoncrossingMatching (c.indexedSigns i)) ≤
      (m+1)^N * (2*r+1)^(8*(r+1-Fintype.card V)) := by
  classical
  obtain ⟨P,hflat,hP,hnum⟩ := c.exists_indexed_tour_fragments block N m hrun hcount hsign
  have h := tokenTour_fragment_matching_count_le (c.indexedTours.map SegmentRoute.tokens) P
    hflat (fun w hw => (hP w hw).2.1) m (2*r) N (8*(r+1-Fintype.card V)) hm
    (fun w hw => (hP w hw).2.2) hnum
  have hlist := congrArg (fun Q : List (SegmentRoute V (Fin (2*r))) =>
      (Q.map (fun p => Nat.card (SignedNoncrossingMatching
        (fun j : Fin p.tokens.length => (p.tokens.get j).2)))).prod)
    (List.ofFn_get c.indexedTours)
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_def] at hlist
  rw [show Nat.card (∀ i : Fin c.indexedTours.length, SignedNoncrossingMatching (c.indexedSigns i)) =
      ∏ i : Fin c.indexedTours.length, Nat.card (SignedNoncrossingMatching (c.indexedSigns i)) by
        simp only [Nat.card_eq_fintype_card,Fintype.card_pi]]
  change (∏ i : Fin c.indexedTours.length, Nat.card (SignedNoncrossingMatching
    (fun j : Fin (c.indexedTours.get i).tokens.length => ((c.indexedTours.get i).tokens.get j).2))) ≤ _
  rw [hlist]
  simpa only [List.map_map,Function.comp_def] using h

#print axioms DefectRouteCertificate.indexedMatching_count_le
end SpectralRadiusUpperTail
