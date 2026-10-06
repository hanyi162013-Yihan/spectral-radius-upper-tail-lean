import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

lemma normalizer_abs_sub_one_le (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg : Integrable g μ) :
    |(∫ x, g x ∂μ)-1| ≤ ∫ x, |g x-1| ∂μ := by
  have h := norm_integral_le_integral_norm (μ := μ) (fun x => g x-1)
  rw [integral_sub hg (integrable_const 1)] at h
  simpa only [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] using h

lemma weighted_normalized_variation_pointwise (g Z f : ℝ) (hZ : 0 < Z) (hf : 0 ≤ f) :
    f * |g/Z-1| ≤ (f * |g-1| + f * |Z-1|) / Z := by
  have heq : g/Z-1 = ((g-1)+(1-Z))/Z := by field_simp; ring
  rw [heq, abs_div, abs_of_pos hZ, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hZ.le
  calc
    f * |(g-1)+(1-Z)| ≤ f * (|g-1|+|1-Z|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hf
    _ = f * |g-1| + f * |Z-1| := by rw [abs_sub_comm 1 Z, mul_add]

/-- Normalizing an almost-constant likelihood has controlled weighted variation.
All Bochner integrability requirements are explicit or proved by domination. -/
theorem weighted_normalized_variation_le (μ : Measure α) [IsProbabilityMeasure μ]
    (g f : α → ℝ) (hg : Integrable g μ) (hf : Integrable f μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (herror : Integrable (fun x => f x * |g x-1|) μ)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun x => f x * |g x/Z-1|) μ ∧
      (∫ x, f x * |g x/Z-1| ∂μ) ≤
        ((∫ x, f x * |g x-1| ∂μ) + |Z-1| * ∫ x, f x ∂μ) / Z := by
  have hdom : Integrable (fun x => (f x * |g x-1| + f x * |Z-1|) / Z) μ :=
    (herror.add (hf.mul_const |Z-1|)).div_const Z
  have hmeas : AEStronglyMeasurable (fun x => f x * |g x/Z-1|) μ := by
    simpa only [Real.norm_eq_abs, Pi.mul_def, Pi.sub_apply] using hf.aestronglyMeasurable.mul
      (((hg.div_const Z).sub (integrable_const 1)).aestronglyMeasurable.norm)
  have hpoint (x : α) := weighted_normalized_variation_pointwise (g x) Z (f x) hZ (hf_nonneg x)
  have hint : Integrable (fun x => f x * |g x/Z-1|) μ :=
    hdom.mono_nonneg hmeas
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hf_nonneg x) (abs_nonneg _)))
      (Filter.Eventually.of_forall hpoint)
  refine ⟨hint, (integral_mono hint hdom hpoint).trans_eq ?_⟩
  rw [integral_div, integral_add herror (hf.mul_const |Z-1|), integral_mul_const]
  rw [mul_comm (∫ x, f x ∂μ)]

theorem weighted_normalized_variation_small (μ : Measure α) [IsProbabilityMeasure μ]
    (g f : α → ℝ) (hg : Integrable g μ) (hf : Integrable f μ)
    (hf_one : ∀ x, 1 ≤ f x) (herror : Integrable (fun x => f x * |g x-1|) μ)
    (ε M : ℝ) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2)
    (herr : (∫ x, f x * |g x-1| ∂μ) ≤ ε) (hM : (∫ x, f x ∂μ) ≤ M) :
    let Z := ∫ x, g x ∂μ
    1/2 ≤ Z ∧ Integrable (fun x => f x * |g x/Z-1|) μ ∧
      (∫ x, f x * |g x/Z-1| ∂μ) ≤ 2*ε*(1+M) := by
  let Z := ∫ x, g x ∂μ
  have hfn (x : α) : 0 ≤ f x := le_trans zero_le_one (hf_one x)
  have hfi : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hfn
  have hMn : 0 ≤ M := hfi.trans hM
  have hraw : (∫ x, |g x-1| ∂μ) ≤ ε := by
    apply (integral_mono ((hg.sub (integrable_const 1)).norm) herror ?_).trans herr
    intro x
    simpa only [Real.norm_eq_abs, Pi.sub_apply, one_mul] using
      mul_le_mul_of_nonneg_right (hf_one x) (abs_nonneg (g x-1))
  have hnorm : |Z-1| ≤ ε := (normalizer_abs_sub_one_le μ g hg).trans hraw
  have hZhalf : 1/2 ≤ Z := by have h := (abs_le.mp hnorm).1; linarith
  have hZ : 0 < Z := lt_of_lt_of_le (by norm_num) hZhalf
  obtain ⟨hint, hbound⟩ := weighted_normalized_variation_le μ g f hg hf hfn herror Z hZ
  refine ⟨hZhalf, hint, hbound.trans ?_⟩
  apply (div_le_iff₀ hZ).mpr
  have hprod : |Z-1| * (∫ x, f x ∂μ) ≤ ε*M :=
    (mul_le_mul_of_nonneg_right hnorm hfi).trans (mul_le_mul_of_nonneg_left hM hε)
  have hmul := mul_le_mul_of_nonneg_left hZhalf (show 0 ≤ 2*ε*(1+M) by positivity)
  nlinarith

#print axioms weighted_normalized_variation_small
end SpectralRadiusUpperTail
