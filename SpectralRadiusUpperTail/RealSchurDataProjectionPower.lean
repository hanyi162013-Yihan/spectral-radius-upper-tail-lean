import SpectralRadiusUpperTail.RealSchurPaddedPowers

namespace SpectralRadiusUpperTail

/-- A padded diagonal power becomes the true one- or two-dimensional block
power after restriction to its active coordinates, including exponent zero. -/
theorem realSchurDataPower_projection (B : RealSchurBlockData)
    (s : ℝ) (m : ℕ) :
    realSchurDataPower B 0 s *
        (realSchurDataPower B 1 s)^m *
        realSchurDataPower B 0 s =
      realSchurDataPower B m s := by
  cases m with
  | zero =>
    simpa only [pow_zero, mul_one] using
      realSchurDataPower_zero_idempotent B s
  | succ m =>
    rw [realSchurDataPower_one_pow_succ,
      realSchurDataPower_zero_left,
      realSchurDataPower_zero_right]

theorem realSchurDataPower_projection_left (B : RealSchurBlockData)
    (s : ℝ) (m : ℕ) :
    realSchurDataPower B 0 s *
        (realSchurDataPower B 1 s)^m *
        realSchurDataPower B 0 s =
      (realSchurDataPower B 1 s)^m * realSchurDataPower B 0 s := by
  cases m with
  | zero =>
    simpa only [pow_zero, mul_one, one_mul] using
      realSchurDataPower_zero_idempotent B s
  | succ m =>
    rw [realSchurDataPower_one_pow_succ,
      realSchurDataPower_zero_left]

theorem realSchurDataPower_projection_right (B : RealSchurBlockData)
    (s : ℝ) (m : ℕ) :
    realSchurDataPower B 0 s *
        (realSchurDataPower B 1 s)^m *
        realSchurDataPower B 0 s =
      realSchurDataPower B 0 s * (realSchurDataPower B 1 s)^m := by
  cases m with
  | zero =>
    simpa only [pow_zero, mul_one] using
      realSchurDataPower_zero_idempotent B s
  | succ m =>
    rw [realSchurDataPower_one_pow_succ,
      mul_assoc,
      realSchurDataPower_zero_right]

#print axioms realSchurDataPower_projection
#print axioms realSchurDataPower_projection_left
#print axioms realSchurDataPower_projection_right
end SpectralRadiusUpperTail
