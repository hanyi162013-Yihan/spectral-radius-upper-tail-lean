import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SpectralRadiusUpperTail

/-- A second-order Taylor bound along a unit segment, proved from three actual
successive derivatives. The conservative factor 1/2 is sufficient for replacement. -/
theorem segment_quadratic_remainder (f f₁ f₂ f₃ : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h₀ : ∀ t, HasDerivAt f (f₁ t) t)
    (h₁ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (h₂ : ∀ t, HasDerivAt f₂ (f₃ t) t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f₃ t| ≤ C) :
    |f 1-(f 0+f₁ 0+(1/2)*f₂ 0)| ≤ C/2 := by
  let Q := fun t => f t+(1-t)*f₁ t+((1-t)^2/2)*f₂ t
  have hQ (t : ℝ) : HasDerivAt Q (((1-t)^2/2)*f₃ t) t := by
    have hc := (hasDerivAt_id t).const_sub 1
    have hcp := (hc.pow 2).div_const 2
    have hh := ((h₀ t).add (hc.mul (h₁ t))).add (hcp.mul (h₂ t))
    convert! hh using 1 <;> (try dsimp only [Pi.pow_apply, id_eq]) <;> ring
  have hQb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖((1-t)^2/2)*f₃ t‖ ≤ C/2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1-t)^2/2)]
    have hc : (1-t)^2/2 ≤ 1/2 := by nlinarith [ht.1, ht.2]
    calc
      _ ≤ (1-t)^2/2*C := mul_le_mul_of_nonneg_left (hbound t ⟨ht.1, ht.2.le⟩) (by positivity)
      _ ≤ (1/2)*C := mul_le_mul_of_nonneg_right hc hC
      _ = _ := by ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hQ t).hasDerivWithinAt) hQb
  simpa [Q, Real.norm_eq_abs] using hh

#print axioms segment_quadratic_remainder
end SpectralRadiusUpperTail
