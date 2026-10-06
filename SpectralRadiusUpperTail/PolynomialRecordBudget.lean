import SpectralRadiusUpperTail.PairRecordCount
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma pairRecordCost_power_budget (N b B g k : ℕ) (hB : 1 ≤ B) (hg : 1 ≤ g)
    (hN : N ≤ B) (hb : b ≤ k*g) (hfactor : b+1 ≤ B) :
    pairRecordCost N b ≤ B^((2*k+1)*g) := by
  have hmax : max 1 (N*N) ≤ B^2 := by
    apply max_le
    · exact Nat.one_le_pow _ _ hB
    · simpa only [pow_two] using Nat.mul_le_mul hN hN
  have hf : b+1 ≤ B^g := hfactor.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right hB hg)
  have hp : (max 1 (N*N))^b ≤ B^(2*k*g) := by
    have h := Nat.pow_le_pow_left hmax b
    rw [← pow_mul] at h
    exact h.trans (Nat.pow_le_pow_right hB (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hb))
  calc
    pairRecordCost N b ≤ B^g * B^(2*k*g) := Nat.mul_le_mul hf hp
    _ = B^((2*k+1)*g) := by rw [← pow_add]; congr 1; ring

#print axioms pairRecordCost_power_budget
end SpectralRadiusUpperTail
