import SpectralRadiusUpperTail.RealGaussianExteriorUnscaledCount
import SpectralRadiusUpperTail.PolynomialComplexPositiveRootNcard
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Undoing the `n⁻¹ᐟ²` normalization in the positive-real-root test
changes the threshold to `r√n` and preserves the real axis. -/
theorem realGaussian_positiveRootPredicate_unscale
    (n : ℕ) (hn : 0 < n) (r : ℝ) (z : ℂ) :
    realGaussianExteriorPredicate r 0
      (((1/Real.sqrt (n : ℝ) : ℝ) : ℂ) * z) ↔
      z.im = 0 ∧ r * Real.sqrt (n : ℝ) < z.re := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hre : ((((1/Real.sqrt (n : ℝ) : ℝ) : ℂ) * z).re) =
      z.re / Real.sqrt (n : ℝ) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  have him : ((((1/Real.sqrt (n : ℝ) : ℝ) : ℂ) * z).im) =
      z.im / Real.sqrt (n : ℝ) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    ring
  simp only [realGaussianExteriorPredicate, ite_true, him, hre]
  constructor
  · rintro ⟨hzero,hlt⟩
    have hz : z.im = 0 := by
      simpa [div_eq_mul_inv, hsqrt.ne'] using hzero
    exact ⟨hz, (lt_div_iff₀ hsqrt).mp hlt⟩
  · rintro ⟨hz,hlt⟩
    exact ⟨by simp [hz], (lt_div_iff₀ hsqrt).mpr hlt⟩

#print axioms realGaussian_positiveRootPredicate_unscale
end SpectralRadiusUpperTail
