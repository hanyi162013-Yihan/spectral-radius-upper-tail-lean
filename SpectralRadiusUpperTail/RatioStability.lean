import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

namespace SpectralRadiusUpperTail

/-- A positive common denominator bound turns actual numerator and denominator
errors into a ratio error, with no small-error assumption. -/
theorem ratio_difference_bound (p q A B J δ₀ δ₁ M : ℝ)
    (hJ : 0 < J) (hA : J ≤ A) (hB : J ≤ B)
    (hden : |A-B| ≤ δ₀) (hnum : |p-q| ≤ δ₁) (hq : |q| ≤ M) :
    |p/A-q/B| ≤ δ₁/J+M*δ₀/J^2 := by
  have hAp : 0 < A := hJ.trans_le hA
  have hBp : 0 < B := hJ.trans_le hB
  have hδ₀ : 0 ≤ δ₀ := (abs_nonneg _).trans hden
  have hδ₁ : 0 ≤ δ₁ := (abs_nonneg _).trans hnum
  have hM : 0 ≤ M := (abs_nonneg _).trans hq
  have he : p/A-q/B = (p-q)/A+q*(B-A)/(A*B) := by
    field_simp <;> ring
  rw [he]
  calc
    _ ≤ |(p-q)/A|+|q*(B-A)/(A*B)| := abs_add_le _ _
    _ = |p-q|/A+|q| * |A-B|/(A*B) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hAp, abs_of_pos (mul_pos hAp hBp), abs_sub_comm B A]
    _ ≤ δ₁/J+M*δ₀/J^2 := by
      apply add_le_add
      · exact div_le_div₀ hδ₁ hnum hJ hA
      · apply div_le_div₀ (mul_nonneg hM hδ₀)
          (mul_le_mul hq hden (abs_nonneg _) hM) (sq_pos_of_pos hJ)
        nlinarith only [mul_le_mul hA hB hJ.le hAp.le]

#print axioms ratio_difference_bound
end SpectralRadiusUpperTail
