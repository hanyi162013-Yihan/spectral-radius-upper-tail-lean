import SpectralRadiusUpperTail.NormalizedVariation
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

lemma abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) :
    |Real.exp x-1| ≤ |x| *Real.exp |x| := by
  by_cases hx : 0 ≤ x
  · have he : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
    have h := Real.add_one_le_exp (-x)
    have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg x)
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero x)] at hm
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonneg hx]
    nlinarith
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have he : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx'
    have h := Real.add_one_le_exp x
    have hE : 1 ≤ Real.exp (-x) := Real.one_le_exp_iff.mpr (neg_nonneg.mpr hx')
    have hm := mul_le_mul_of_nonneg_left hE (neg_nonneg.mpr hx')
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos hx']
    nlinarith

lemma exp_variation_pointwise (D B u : ℝ) (hB : 0 ≤ B) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hD : |D| ≤ u*B) : |Real.exp D-1| ≤ u*B*Real.exp B := by
  have hDB : |D| ≤ B := hD.trans (by nlinarith)
  exact (abs_exp_sub_one_le_abs_mul_exp_abs D).trans
    (mul_le_mul hD (Real.exp_le_exp.mpr hDB) (Real.exp_nonneg _) (mul_nonneg hu hB))

/-- An integrable exponential envelope turns a pointwise logarithmic perturbation
into a linear weighted likelihood error. -/
theorem exponential_weighted_error (μ : Measure α) [IsProbabilityMeasure μ]
    (D B f : α → ℝ) (hD : Measurable D) (hf : Measurable f)
    (hB : ∀ x, 0 ≤ B x) (hf1 : ∀ x, 1 ≤ f x)
    (henv : Integrable (fun x => f x*B x*Real.exp (B x)) μ)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hlog : ∀ x, |D x| ≤ u*B x) :
    Integrable (fun x => Real.exp (D x)) μ ∧
      Integrable (fun x => f x*|Real.exp (D x)-1|) μ ∧
      (∫ x, f x*|Real.exp (D x)-1| ∂μ) ≤
        u * ∫ x, f x*B x*Real.exp (B x) ∂μ := by
  have hfn (x : α) : 0 ≤ f x := le_trans zero_le_one (hf1 x)
  have hp (x : α) : f x*|Real.exp (D x)-1| ≤ u*(f x*B x*Real.exp (B x)) := by
    have h := mul_le_mul_of_nonneg_left
      (exp_variation_pointwise (D x) (B x) u (hB x) hu hu1 (hlog x)) (hfn x)
    nlinarith only [h]
  have habs : Measurable (fun x => |Real.exp (D x)-1|) := by
    simpa only [Real.norm_eq_abs] using
      (show Measurable (fun x => Real.exp (D x)-1) from
        (Real.measurable_exp.comp hD).sub measurable_const).norm
  have hi := (henv.const_mul u).mono_nonneg (hf.mul habs).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => mul_nonneg (hfn x) (abs_nonneg _)))
    (Filter.Eventually.of_forall hp)
  have hg : Integrable (fun x => Real.exp (D x)) μ := by
    apply ((integrable_const 1).add (henv.const_mul u)).mono'
      (Real.measurable_exp.comp hD).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖Real.exp (D x)‖ ≤ 1 + u*(f x*B x*Real.exp (B x))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hraw := mul_le_mul_of_nonneg_right (hf1 x) (abs_nonneg (Real.exp (D x)-1))
    have hab := le_abs_self (Real.exp (D x)-1)
    have hp' := hp x
    nlinarith
  refine ⟨hg, hi, (integral_mono hi (henv.const_mul u) hp).trans_eq ?_⟩
  exact integral_const_mul u _

#print axioms exponential_weighted_error
end SpectralRadiusUpperTail
