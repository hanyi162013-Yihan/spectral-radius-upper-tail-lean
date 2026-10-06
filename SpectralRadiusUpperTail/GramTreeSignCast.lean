import SpectralRadiusUpperTail.GramSignMatchingCount

namespace SpectralRadiusUpperTail

lemma signedMatching_card_cast {n k : ℕ} (h : n = k) (s : Fin k → Bool) :
    Nat.card (SignedNoncrossingMatching (fun i : Fin n => s (Fin.cast h i))) =
      Nat.card (SignedNoncrossingMatching s) := by
  subst k
  rfl

/-- The actual Gram signs indexed with half-length r=q*m. -/
def gramTreeSign (m q : ℕ) (i : Fin (2*(q*m))) : Bool :=
  gramFiniteSign m q (Fin.cast (Nat.mul_assoc 2 q m).symm i)

lemma gramTreeSign_matching_count_le (m q : ℕ) :
    Nat.card (SignedNoncrossingMatching (gramTreeSign m q)) ≤ (m+1)^(2*q) := by
  unfold gramTreeSign
  rw [signedMatching_card_cast]
  exact gramSign_matching_count_le m q

#print axioms signedMatching_card_cast
#print axioms gramTreeSign
#print axioms gramTreeSign_matching_count_le
end SpectralRadiusUpperTail
