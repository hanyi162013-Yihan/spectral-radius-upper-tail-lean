import SpectralRadiusUpperTail.MarkedRealGaussianCharpolyMomentReal
import SpectralRadiusUpperTail.GaussianMarkedRealNormalization

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- The unscaled real-eigenvalue one-point integrand in dimension m+1. -/
noncomputable def gaussianMarkedRealUnscaledWeight (m : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ)^(-(((m : ℝ)+1)/2)) /
    Real.Gamma (((m : ℝ)+1)/2)) *
    ENNReal.ofReal (Real.exp (-x^2/2)) * markedRealGaussianCharpolyMoment m x

theorem gaussianMarkedRealUnscaledWeight_rescale
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (Real.sqrt ((m+1 : ℕ) : ℝ)) *
      gaussianMarkedRealUnscaledWeight m (Real.sqrt ((m+1 : ℕ) : ℝ)*r) =
      ENNReal.ofReal (gaussianMarkedRealDensity (m+1) r) := by
  have hs : (Real.sqrt ((m+1 : ℕ) : ℝ) * r)^2 = ((m+1 : ℕ) : ℝ)*r^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hc : 0 ≤ (2 : ℝ)^(-(((m : ℝ)+1)/2)) / Real.Gamma (((m : ℝ)+1)/2) := by
    apply div_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
    exact (Real.Gamma_pos_of_pos (by positivity)).le
  rw [gaussianMarkedRealDensity_eq_kacRice_moment (m+1) (by omega) r hr]
  simp only [Nat.cast_add, Nat.cast_one]
  unfold gaussianMarkedRealUnscaledWeight
  rw [markedRealGaussianCharpolyMoment_eq_ofReal_integral]
  have he : Real.exp (-(Real.sqrt (((m : ℝ)+1))*r)^2/2) =
      Real.exp (-((m : ℝ)+1)*r^2/2) := by
    have hs' : (Real.sqrt ((m : ℝ)+1)*r)^2 = ((m : ℝ)+1)*r^2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hs
    rw [hs', neg_mul]
  rw [he]
  rw [← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) hc),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hc) (Real.exp_nonneg _))]
  congr 1
  apply congrArg₂ (fun a b : ℝ => a*b)
  · ring
  · rfl

#print axioms gaussianMarkedRealUnscaledWeight_rescale
end SpectralRadiusUpperTail
