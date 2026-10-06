import SpectralRadiusUpperTail.RealSchurPadding

namespace SpectralRadiusUpperTail

/-- The padded zeroth power is the identity on the actual one- or two-dimensional block. -/
lemma realSchurDataPower_zero_left (B : RealSchurBlockData) (k : ℕ) (s : ℝ) :
    realSchurDataPower B 0 s * realSchurDataPower B k s =
      realSchurDataPower B k s := by
  simpa using (realSchurDataPower_add B 0 k s).symm

lemma realSchurDataPower_zero_right (B : RealSchurBlockData) (k : ℕ) (s : ℝ) :
    realSchurDataPower B k s * realSchurDataPower B 0 s =
      realSchurDataPower B k s := by
  simpa using (realSchurDataPower_add B k 0 s).symm

lemma realSchurDataPower_zero_idempotent (B : RealSchurBlockData) (s : ℝ) :
    realSchurDataPower B 0 s * realSchurDataPower B 0 s =
      realSchurDataPower B 0 s :=
  realSchurDataPower_zero_left B 0 s

#print axioms realSchurDataPower_zero_left
#print axioms realSchurDataPower_zero_right
end SpectralRadiusUpperTail
