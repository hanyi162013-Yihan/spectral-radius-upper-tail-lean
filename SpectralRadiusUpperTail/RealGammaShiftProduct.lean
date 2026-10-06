import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- A finite Gamma shift is exactly a rising product. This avoids importing
any asymptotic Gamma ratio formula into the Ginibre calculation. -/
theorem real_gamma_add_nat_product (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Real.Gamma (a+(k : ℝ)) =
      Real.Gamma a * ∏ j ∈ Finset.range k, (a+(j : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hak : a+(k : ℝ) ≠ 0 := by positivity
    calc
      Real.Gamma (a+(k+1 : ℕ)) = Real.Gamma ((a+(k : ℝ))+1) := by
        congr 1
        push_cast
        ring
      _ = (a+(k : ℝ))*Real.Gamma (a+(k : ℝ)) :=
        Real.Gamma_add_one hak
      _ = Real.Gamma a * (∏ j ∈ Finset.range k, (a+(j : ℝ))) *
          (a+(k : ℝ)) := by rw [ih]; ring
      _ = Real.Gamma a * ∏ j ∈ Finset.range (k+1), (a+(j : ℝ)) := by
        rw [Finset.prod_range_succ]
        ring

/-- Shifting both Gamma arguments up by one only enlarges a positive
integer-step ratio. -/
theorem real_gamma_ratio_le_shifted (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Real.Gamma (a+(k : ℝ))/Real.Gamma a ≤
      Real.Gamma (a+(k : ℝ)+1)/Real.Gamma (a+1) := by
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hak : 0 < a+(k : ℝ) := by positivity
  have hGk : 0 < Real.Gamma (a+(k : ℝ)) :=
    Real.Gamma_pos_of_pos hak
  rw [Real.Gamma_add_one ha.ne', Real.Gamma_add_one hak.ne']
  apply (div_le_div_iff₀ hG (mul_pos ha hG)).mpr
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity) hGk.le]

#print axioms real_gamma_add_nat_product
#print axioms real_gamma_ratio_le_shifted
end SpectralRadiusUpperTail
