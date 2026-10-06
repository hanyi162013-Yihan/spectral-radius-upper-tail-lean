import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma log_positive_shift_gap (x s M : ℝ) (hx : 0 < x) (hs : 0 ≤ s)
    (hM : x⁻¹ ≤ M) : Real.log (x+s)-Real.log x ≤ s*M := by
  have hh := Real.log_le_sub_one_of_pos (show 0 < (x+s)/x by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hx)] at hh
  have he : (x+s)/x-1 = s*x⁻¹ := by field_simp; ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hM hs)

lemma log_product_positive_shift_gap {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (s M : ℝ) (hh : ∀ i, 0 < h i) (hs : 0 ≤ s)
    (hM : ∀ i, (h i)⁻¹ ≤ M) :
    Real.log (∏ i, (h i+s))-Real.log (∏ i, h i) ≤ (Fintype.card ι : ℝ)*s*M := by
  rw [Real.log_prod (fun i _ => ne_of_gt (add_pos_of_pos_of_nonneg (hh i) hs)),
    Real.log_prod (fun i _ => ne_of_gt (hh i)), ← Finset.sum_sub_distrib]
  have he := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    log_positive_shift_gap (h i) s M (hh i) hs (hM i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using he

#print axioms log_positive_shift_gap
#print axioms log_product_positive_shift_gap
end SpectralRadiusUpperTail
