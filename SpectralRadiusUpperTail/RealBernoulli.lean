import SpectralRadiusUpperTail.FourPoint
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.NormNum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def signMeasure : Measure ℝ :=
  (1/2 : ℝ≥0∞) • (Measure.dirac 1 + Measure.dirac (-1))

lemma sign_integrable (f : ℝ → ℝ) : Integrable f signMeasure := by
  have h (a : ℝ) : Integrable f (Measure.dirac a) := integrable_dirac (by simp)
  exact ((h 1).add_measure (h (-1))).smul_measure (by norm_num)

lemma integral_sign (f : ℝ → ℝ) :
    (∫ x, f x ∂signMeasure) = (f 1+f (-1))/2 := by
  have h (a : ℝ) : Integrable f (Measure.dirac a) := integrable_dirac (by simp)
  rw [signMeasure, integral_smul_measure]
  simp [integral_add_measure, h, integral_dirac]
  ring

instance sign_isProbabilityMeasure : IsProbabilityMeasure signMeasure := by
  constructor
  norm_num [signMeasure, Measure.add_apply, Measure.smul_apply]
  calc
    (2:ℝ≥0∞)⁻¹+(2:ℝ≥0∞)⁻¹ = 2*(2:ℝ≥0∞)⁻¹ := by ring
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem sign_centered : (∫ x : ℝ, x ∂signMeasure) = 0 := by
  rw [integral_sign]; norm_num

theorem sign_even_moment (m : ℕ) :
    (∫ x : ℝ, x^(2*m) ∂signMeasure) = 1 := by
  rw [integral_sign]
  simp [pow_mul]

theorem sign_odd_moment (m : ℕ) :
    (∫ x : ℝ, x^(2*m+1) ∂signMeasure) = 0 := by
  rw [integral_sign]
  simp [pow_add, pow_mul]

/-- Every Gaussian even-moment hypothesis is verified for the actual sign law. -/
theorem sign_gaussian_moment_domination (m : ℕ) :
    (∫ x : ℝ, x^(2*m) ∂signMeasure) ≤ (Nat.doubleFactorial (2*m-1) : ℝ) := by
  rw [sign_even_moment]
  exact_mod_cast Nat.doubleFactorial_pos (2*m-1)

theorem sign_laplace (t : ℝ) :
    (∫ x : ℝ, Real.exp (t*x) ∂signMeasure) ≤ Real.exp (t^2/2) := by
  rw [integral_sign]
  simpa [signMGF] using signMGF_le t

#print axioms sign_isProbabilityMeasure
#print axioms sign_gaussian_moment_domination
#print axioms sign_laplace
end SpectralRadiusUpperTail
