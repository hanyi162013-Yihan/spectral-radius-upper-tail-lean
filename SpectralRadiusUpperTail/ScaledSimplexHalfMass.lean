import SpectralRadiusUpperTail.SimplexHalfMass

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable def positiveSimplexAt (m : ℕ) (T : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ T}

lemma positiveSimplexAt_measurable (m : ℕ) (T : ℝ) : MeasurableSet (positiveSimplexAt m T) := by
  change MeasurableSet ({x : Fin m → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ T})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (show Measurable (fun x : Fin m → ℝ => ∑ i, x i) by fun_prop) measurable_const

lemma scaled_simplex_mass_ge_half (m : ℕ) (T : ℝ) (hT : 0 < T)
    (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (hcoord : ∀ᵐ x ∂P, ∀ i, 0 ≤ x i)
    (hmean : (∫⁻ x, ∑ i : Fin m, ENNReal.ofReal (x i) ∂P) ≤ ENNReal.ofReal (T/2)) :
    (1/2 : ℝ≥0∞) ≤ P (positiveSimplexAt m T) := by
  have hm : Measurable (fun x : Fin m → ℝ => ∑ i, ENNReal.ofReal (x i)) := by fun_prop
  have hmark := (mul_meas_ge_le_lintegral (μ := P) hm (ENNReal.ofReal T)).trans hmean
  have ht := mul_le_mul' (le_refl ((ENNReal.ofReal T)⁻¹)) hmark
  rw [← mul_assoc, ENNReal.inv_mul_cancel ((ENNReal.ofReal_pos.mpr hT).ne')
    ENNReal.ofReal_ne_top, one_mul] at ht
  have he : (ENNReal.ofReal T)⁻¹*ENNReal.ofReal (T/2) = (1/2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_inv_of_pos hT, ← ENNReal.ofReal_mul (inv_nonneg.mpr hT.le)]
    have hr : T⁻¹*(T/2) = (1/2 : ℝ) := by field_simp
    rw [hr]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [he] at ht
  have hsub : ∀ᵐ x ∂P, x ∈ (positiveSimplexAt m T)ᶜ →
      x ∈ {y | ENNReal.ofReal T ≤ ∑ i, ENNReal.ofReal (y i)} := by
    filter_upwards [hcoord] with x hx
    intro hnot
    have hs : T < ∑ i : Fin m, x i := by
      apply lt_of_not_ge
      intro hh
      exact hnot ⟨hx, hh⟩
    have hh := ENNReal.ofReal_le_ofReal hs.le
    simpa only [ENNReal.ofReal_sum_of_nonneg (fun i _ => hx i)] using hh
  have hb : P (positiveSimplexAt m T)ᶜ ≤ 1/2 :=
    (measure_mono_ae (s := (positiveSimplexAt m T)ᶜ)
      (t := {x | ENNReal.ofReal T ≤ ∑ i, ENNReal.ofReal (x i)}) hsub).trans ht
  have hh := tsub_le_tsub_left hb (1 : ℝ≥0∞)
  rw [show (1 : ℝ≥0∞)-1/2 = 1/2 by norm_num,
    ← prob_compl_eq_one_sub (positiveSimplexAt_measurable m T).compl, compl_compl] at hh
  exact hh

#print axioms positiveSimplexAt
#print axioms positiveSimplexAt_measurable
#print axioms scaled_simplex_mass_ge_half
end SpectralRadiusUpperTail
