import SpectralRadiusUpperTail.LowerMeanFromProbability

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A bounded observable concentrated around any deterministic center has its
mean close to that center. This applies in particular to a median. -/
lemma bounded_mean_distance_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hi : Integrable f μ) (m B t : ℝ) (ht : 0 ≤ t)
    (hB : ∀ᵐ x ∂μ, |f x-m| ≤ B) :
    |(∫ x, f x ∂μ)-m| ≤ t+B*μ.real {x | t < |f x-m|} := by
  classical
  let E := {x | t < |f x-m|}
  have hE : MeasurableSet E := by
    exact measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using (hf.sub_const m).norm)
  have hInd : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const _).indicator hE
  have hpoint : ∀ᵐ x ∂μ, |f x-m| ≤ t+B*E.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hB] with x hx
    by_cases he : x ∈ E
    · rw [Set.indicator_of_mem he, mul_one]
      linarith
    · rw [Set.indicator_of_notMem he, mul_zero, add_zero]
      exact le_of_not_gt he
  have hiabs : Integrable (fun x => |f x-m|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hi.sub (integrable_const m)).norm
  have hh := integral_mono_ae hiabs ((integrable_const t).add (hInd.const_mul B)) hpoint
  change (∫ x, |f x-m| ∂μ) ≤ ∫ x, t+B*E.indicator (fun _ => (1 : ℝ)) x ∂μ at hh
  rw [integral_add (integrable_const t) (hInd.const_mul B), integral_const,
    integral_const_mul, integral_indicator_const (1 : ℝ) hE] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one] at hh
  have hm : (∫ x, f x ∂μ)-m = ∫ x, f x-m ∂μ := by
    rw [integral_sub hi (integrable_const m), integral_const]
    simp
  rw [hm]
  exact abs_integral_le_integral_abs.trans hh

lemma centered_tail_le_center_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (m δ : ℝ)
    (hm : |(∫ x, f x ∂μ)-m| ≤ δ/2) :
    μ.real {x | δ < |f x-(∫ y, f y ∂μ)|} ≤ μ.real {x | δ/2 < |f x-m|} := by
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  change δ < |f x-(∫ y, f y ∂μ)| at hx
  change δ/2 < |f x-m|
  have hh : |f x-(∫ y, f y ∂μ)| ≤ |f x-m|+|(∫ y, f y ∂μ)-m| := by
    calc
      _ = |(f x-m)-((∫ y, f y ∂μ)-m)| := by congr 1; ring
      _ ≤ _ := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (f x-m) 0 ((∫ y, f y ∂μ)-m)
  linarith

#print axioms bounded_mean_distance_of_tail
#print axioms centered_tail_le_center_tail
end SpectralRadiusUpperTail
