import SpectralRadiusUpperTail.SharpDefectCodeCount
import SpectralRadiusUpperTail.PolynomialRecordBudget

namespace SpectralRadiusUpperTail

lemma defectCodeCost_power_le (L g : ℕ) (hg : 1 ≤ g) (hgL : g ≤ L) :
    defectCodeCost L g ≤ (64*(L+1))^(64*g) := by
  let B := 64*(L+1)
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hL : L+1 ≤ B := by dsimp [B]; omega
  have hlarge : 8*g+2 ≤ B := by dsimp [B]; omega
  have hshape : 4*(8*g+1) ≤ B := by dsimp [B]; omega
  have hpref (a : ℕ) (ha : a ≤ B) : a ≤ B^g :=
    ha.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hB hg)
  have hout : 8*g+2 ≤ B^g := hpref _ hlarge
  have hdel : (8*g+1)*(max 1 L)^(8*g) ≤ B^(9*g) := by
    calc
      _ ≤ B^g * B^(8*g) := Nat.mul_le_mul (hpref _ (by omega))
        (Nat.pow_le_pow_left (by omega : max 1 L ≤ B) _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hpow1 : (L+1)^(8*g+1) ≤ B^(9*g) :=
    (Nat.pow_le_pow_left hL _).trans (Nat.pow_le_pow_right hB (by omega))
  have hpow2 : (max 1 (4*(8*g+1)))^(8*g+1) ≤ B^(9*g) :=
    (Nat.pow_le_pow_left (max_le hB hshape) _).trans (Nat.pow_le_pow_right hB (by omega))
  have hs : (L+1)^(8*g+1) * (max 1 (4*(8*g+1)))^(8*g+1) ≤ B^(18*g) := by
    calc
      _ ≤ B^(9*g)*B^(9*g) := Nat.mul_le_mul hpow1 hpow2
      _ = _ := by rw [← pow_add]; congr 1; omega
  have he : pairRecordCost (2*L) (8*g) ≤ B^(17*g) :=
    pairRecordCost_power_budget (2*L) (8*g) B g 8 hB hg (by dsimp [B]; omega) le_rfl (by omega)
  have hf : pairRecordCost (L+1) (8*g+1) ≤ B^(19*g) :=
    pairRecordCost_power_budget (L+1) (8*g+1) B g 9 hB hg hL (by omega) hlarge
  calc
    defectCodeCost L g ≤ B^g*(B^(9*g)*B^(18*g))*(B^(17*g)*B^(19*g)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hout (Nat.mul_le_mul hdel hs)) (Nat.mul_le_mul he hf)
    _ = B^(64*g) := by simp only [← pow_add]; congr 1; omega

#print axioms defectCodeCost_power_le
end SpectralRadiusUpperTail
