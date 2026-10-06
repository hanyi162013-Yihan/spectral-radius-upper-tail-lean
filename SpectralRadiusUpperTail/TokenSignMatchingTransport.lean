import SpectralRadiusUpperTail.ListSignMatchingTransport

namespace SpectralRadiusUpperTail
variable {A : Type*}

lemma tokenSigns_ofFn (w : List (A × Bool)) :
    List.ofFn (fun i : Fin w.length => (w.get i).2) = w.map Prod.snd := by
  have h := congrArg (List.map Prod.snd) (List.ofFn_get w)
  simpa only [List.map_ofFn,Function.comp_def] using h

lemma tokenSignMatching_card (w : List (A × Bool)) :
    Nat.card (SignedNoncrossingMatching (fun i : Fin w.length => (w.get i).2)) =
      Nat.card (SignedNoncrossingMatching (fun i : Fin (w.map Prod.snd).length =>
        (w.map Prod.snd).get i)) := by
  rw [← tokenSigns_ofFn]
  exact (listSignMatchingCard_ofFn _).symm

#print axioms tokenSigns_ofFn
#print axioms tokenSignMatching_card
end SpectralRadiusUpperTail
