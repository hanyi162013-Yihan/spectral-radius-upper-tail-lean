import SpectralRadiusUpperTail.RealSchurPaddedPowers

namespace SpectralRadiusUpperTail

/-- Once a path carries its diagonal-block powers, the artificial
two-dimensional projections on a Gaussian bridge cancel exactly. -/
theorem realSchur_padded_bridge_cancel
    (Bi Bj : RealSchurBlockData) (si sj : ℝ) (a b : ℕ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) :
    realSchurDataPower Bi a si *
        (realSchurDataPower Bi 0 si * G * realSchurDataPower Bj 0 sj) *
        realSchurDataPower Bj b sj =
      realSchurDataPower Bi a si * G * realSchurDataPower Bj b sj := by
  calc
    _ = (realSchurDataPower Bi a si * realSchurDataPower Bi 0 si) * G *
        (realSchurDataPower Bj 0 sj * realSchurDataPower Bj b sj) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [realSchurDataPower_zero_right, realSchurDataPower_zero_left]

theorem realSchurPaddedBridge_cancel {N : ℕ} (n : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ))
    (i j : Fin N) (a b : ℕ) :
    realSchurDataPower (B i) a (z.1 i) * realSchurPaddedBridge n B z i j *
        realSchurDataPower (B j) b (z.1 j) =
      realSchurDataPower (B i) a (z.1 i) *
        ((1/Real.sqrt n) • Matrix.of (fun r s => z.2 ((i,j),(r,s)))) *
        realSchurDataPower (B j) b (z.1 j) := by
  exact realSchur_padded_bridge_cancel (B i) (B j) (z.1 i) (z.1 j) a b _

#print axioms realSchur_padded_bridge_cancel
#print axioms realSchurPaddedBridge_cancel
end SpectralRadiusUpperTail
