import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact Laplace-transform checks for the real signs and the four complex roots
of unity. These are distribution-level hypotheses, not a matrix LDP. -/
namespace SpectralRadiusUpperTail

noncomputable def signMGF (t : ℝ) : ℝ := (Real.exp t + Real.exp (-t)) / 2

noncomputable def fourPointMGF (a b : ℝ) : ℝ :=
  (Real.exp (2*a) + Real.exp (-2*a) + Real.exp (2*b) + Real.exp (-2*b)) / 4

theorem signMGF_le (t : ℝ) : signMGF t ≤ Real.exp (t^2/2) := by
  simpa [signMGF, Real.cosh_eq] using Real.cosh_le_exp_half_sq t

theorem fourPointMGF_eq (a b : ℝ) :
    fourPointMGF a b = Real.cosh (a+b) * Real.cosh (a-b) := by
  rw [Real.cosh_eq, Real.cosh_eq]
  unfold fourPointMGF
  have h₁ : Real.exp (a+b) * Real.exp (a-b) = Real.exp (2*a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₂ : Real.exp (a+b) * Real.exp (-(a-b)) = Real.exp (2*b) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₃ : Real.exp (-(a+b)) * Real.exp (a-b) = Real.exp (-2*b) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₄ : Real.exp (-(a+b)) * Real.exp (-(a-b)) = Real.exp (-2*a) := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith

theorem fourPointMGF_le (a b : ℝ) : fourPointMGF a b ≤ Real.exp (a^2+b^2) := by
  rw [fourPointMGF_eq]
  calc
    Real.cosh (a+b) * Real.cosh (a-b)
        ≤ Real.exp ((a+b)^2/2) * Real.exp ((a-b)^2/2) :=
      mul_le_mul (Real.cosh_le_exp_half_sq _) (Real.cosh_le_exp_half_sq _)
        (le_of_lt (Real.cosh_pos _)) (le_of_lt (Real.exp_pos _))
    _ = Real.exp (a^2+b^2) := by rw [← Real.exp_add]; congr 1; ring

#print axioms signMGF_le
#print axioms fourPointMGF_eq
#print axioms fourPointMGF_le
end SpectralRadiusUpperTail
