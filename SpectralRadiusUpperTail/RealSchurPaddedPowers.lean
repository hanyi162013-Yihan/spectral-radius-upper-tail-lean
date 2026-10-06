import SpectralRadiusUpperTail.RealSchurPaddedDuhamel

namespace SpectralRadiusUpperTail

/-- Positive powers of the padded diagonal block coincide with the
embedded power of the actual Schur block. -/
theorem realSchurDataPower_one_pow_succ (B : RealSchurBlockData) (s : ℝ) (k : ℕ) :
    (realSchurDataPower B 1 s)^(k+1) = realSchurDataPower B (k+1) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simpa only [Nat.add_assoc] using (realSchurDataPower_add B (k+1) 1 s).symm

/-- The bridge projection makes the zeroth waiting power in the padded
matrix agree with the actual block's padded zeroth power. -/
theorem realSchurPaddedBridge_left_waiting {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) (k : ℕ) :
    (realSchurDataPower (B i) 1 (z.1 i))^k * realSchurPaddedBridge n B z i j =
      realSchurDataPower (B i) k (z.1 i) * realSchurPaddedBridge n B z i j := by
  cases k with
  | zero =>
    simpa only [pow_zero, one_mul] using
      (realSchurPaddedBridge_left_support n B z i j).symm
  | succ k => rw [realSchurDataPower_one_pow_succ]

theorem realSchurPaddedBridge_right_waiting {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) (k : ℕ) :
    realSchurPaddedBridge n B z i j * (realSchurDataPower (B j) 1 (z.1 j))^k =
      realSchurPaddedBridge n B z i j * realSchurDataPower (B j) k (z.1 j) := by
  cases k with
  | zero =>
    simpa only [pow_zero, mul_one] using
      (realSchurPaddedBridge_right_support n B z i j).symm
  | succ k => rw [realSchurDataPower_one_pow_succ]

#print axioms realSchurDataPower_one_pow_succ
#print axioms realSchurPaddedBridge_left_waiting
#print axioms realSchurPaddedBridge_right_waiting
end SpectralRadiusUpperTail
