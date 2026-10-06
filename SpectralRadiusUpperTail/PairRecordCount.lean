import SpectralRadiusUpperTail.BoundedFinsetCount

namespace SpectralRadiusUpperTail

def pairRecordCost (N b : ℕ) := (b+1)*(max 1 (N*N))^b

lemma bounded_pair_record_count {A : Type*} [Fintype A] [DecidableEq A]
    (N b : ℕ) (hN : Fintype.card A ≤ N) :
    Nat.card {E : Finset (A × A) // E.card ≤ b} ≤ pairRecordCost N b := by
  have h := bounded_card_finset_count (A := A × A) b
  rw [Fintype.card_prod] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (max_le_max_left 1 (Nat.mul_le_mul hN hN)) b))

#print axioms pairRecordCost
#print axioms bounded_pair_record_count
end SpectralRadiusUpperTail
