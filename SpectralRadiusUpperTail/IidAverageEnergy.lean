import SpectralRadiusUpperTail.FiniteAverageSecondMoment
import SpectralRadiusUpperTail.ProductRowEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

noncomputable def averageEntryEnergy {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (x : ι → E) : ℝ := (∑ i, ‖x i‖^2)/(Fintype.card ι : ℝ)

lemma averageEntryEnergy_nonneg {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (x : ι → E) : 0 ≤ averageEntryEnergy x := by unfold averageEntryEnergy; positivity

lemma averageEntryEnergy_sq_le {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] (x : ι → E) :
    averageEntryEnergy x^2 ≤ (∑ i, ‖x i‖^4)/(Fintype.card ι : ℝ) := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖x i‖^2)
  simp only [Finset.card_univ, ← pow_mul, show (2:ℕ)*2=4 by norm_num] at hh
  unfold averageEntryEnergy
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hc 2)).mpr
  convert! hh using 1
  field_simp

lemma iid_averageEntryEnergy_secondMoment {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (h4 : Integrable (fun z : ℂ => ‖z‖^4) μ) :
    Integrable (fun x : ι → ℂ => averageEntryEnergy x^2) (Measure.pi (fun _ => μ)) ∧
      (∫ x : ι → ℂ, averageEntryEnergy x^2 ∂Measure.pi (fun _ => μ)) ≤
        ∫ z : ℂ, ‖z‖^4 ∂μ := by
  have hi (i : ι) : Integrable (fun x : ι → ℂ => ‖x i‖^4) (Measure.pi (fun _ => μ)) :=
    (measurePreserving_eval (fun _ : ι => μ) i).integrable_comp_of_integrable h4
  have hdom := (integrable_finsetSum Finset.univ (fun i _ => hi i)).div_const (Fintype.card ι : ℝ)
  have hf : Integrable (fun x : ι → ℂ => averageEntryEnergy x^2) (Measure.pi (fun _ => μ)) := by
    have hm : Measurable (fun x : ι → ℂ => averageEntryEnergy x^2) := by
      unfold averageEntryEnergy
      fun_prop
    apply hdom.mono' hm.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact averageEntryEnergy_sq_le x
  refine ⟨hf, (integral_mono hf hdom (fun x => averageEntryEnergy_sq_le x)).trans_eq ?_⟩
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_product_coordinate μ _ _ h4.aestronglyMeasurable]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  field_simp

#print axioms averageEntryEnergy
#print axioms averageEntryEnergy_nonneg
#print axioms averageEntryEnergy_sq_le
#print axioms iid_averageEntryEnergy_secondMoment
end SpectralRadiusUpperTail
