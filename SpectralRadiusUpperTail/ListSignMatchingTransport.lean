import SpectralRadiusUpperTail.ConcatenateSignedMatchings
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail

noncomputable def finiteSignMatchingCard (w : FiniteSignWord) := Nat.card (SignedNoncrossingMatching w.2)

lemma listSignMatchingCard_ofFn {n : ℕ} (s : Fin n → Bool) :
    Nat.card (SignedNoncrossingMatching (fun i : Fin (List.ofFn s).length => (List.ofFn s).get i)) =
      Nat.card (SignedNoncrossingMatching s) := by
  exact congrArg finiteSignMatchingCard (List.equivSigmaTuple.apply_symm_apply ⟨n,s⟩)

lemma concatenateSigns_ofFn (W : List FiniteSignWord) :
    List.ofFn (concatenateSigns W) = W.flatMap (fun w => List.ofFn w.2) := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    change List.ofFn (Fin.addCases w.2 (concatenateSigns W)) = List.ofFn w.2 ++ _
    rw [List.ofFn_add]
    have hl (i : Fin w.1) : Fin.addCases w.2 (concatenateSigns W)
        (i.castLE (Nat.le_add_right w.1 (signWordLength W))) = w.2 i := Fin.addCases_left i
    simp only [hl,Fin.addCases_right]
    change List.ofFn w.2 ++ List.ofFn (concatenateSigns W) = List.ofFn w.2 ++ _
    rw [ih,List.flatMap_def]

lemma concatenateSigns_listMatchingCard (W : List FiniteSignWord) :
    Nat.card (SignedNoncrossingMatching (concatenateSigns W)) =
      Nat.card (SignedNoncrossingMatching
        (fun i : Fin (W.flatMap (fun w => List.ofFn w.2)).length =>
          (W.flatMap (fun w => List.ofFn w.2)).get i)) := by
  rw [← concatenateSigns_ofFn]
  exact (listSignMatchingCard_ofFn _).symm

#print axioms finiteSignMatchingCard
#print axioms listSignMatchingCard_ofFn
#print axioms concatenateSigns_ofFn
#print axioms concatenateSigns_listMatchingCard
end SpectralRadiusUpperTail
