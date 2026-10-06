import SpectralRadiusUpperTail.ExponentialFirstMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable def positiveSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

lemma positiveSimplex_measurable (m : ℕ) : MeasurableSet (positiveSimplex m) := by
  change MeasurableSet ({x : Fin m → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (show Measurable (fun x : Fin m → ℝ => ∑ i, x i) by fun_prop) measurable_const

lemma simplex_mass_ge_half (m : ℕ) (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (hcoord : ∀ᵐ x ∂P, ∀ i, 0 ≤ x i)
    (hmean : (∫⁻ x, ∑ i : Fin m, ENNReal.ofReal (x i) ∂P) ≤ 1/2) :
    (1/2 : ℝ≥0∞) ≤ P (positiveSimplex m) := by
  have hm : Measurable (fun x : Fin m → ℝ => ∑ i, ENNReal.ofReal (x i)) := by fun_prop
  have hmark := mul_meas_ge_le_lintegral (μ := P) hm 1
  simp only [one_mul] at hmark
  have hsub : ∀ᵐ x ∂P, x ∈ (positiveSimplex m)ᶜ → x ∈ {y | (1 : ℝ≥0∞) ≤ ∑ i, ENNReal.ofReal (y i)} := by
    filter_upwards [hcoord] with x hx
    intro hnot
    have hs : 1 < ∑ i : Fin m, x i := by
      apply lt_of_not_ge
      intro hh
      exact hnot ⟨hx,hh⟩
    change (1 : ℝ≥0∞) ≤ ∑ i, ENNReal.ofReal (x i)
    have hh := ENNReal.ofReal_le_ofReal hs.le
    simpa only [ENNReal.ofReal_one,ENNReal.ofReal_sum_of_nonneg (fun i _ => hx i)] using hh
  have hb : P (positiveSimplex m)ᶜ ≤ 1/2 :=
    (measure_mono_ae (s := (positiveSimplex m)ᶜ)
      (t := {x | (1 : ℝ≥0∞) ≤ ∑ i, ENNReal.ofReal (x i)}) hsub).trans (hmark.trans hmean)
  have ht := tsub_le_tsub_left hb (1 : ℝ≥0∞)
  have he : (1 : ℝ≥0∞)-1/2 = 1/2 := by norm_num
  rw [he,← prob_compl_eq_one_sub (positiveSimplex_measurable m).compl,compl_compl] at ht
  exact ht

#print axioms positiveSimplex
#print axioms positiveSimplex_measurable
#print axioms simplex_mass_ge_half
end SpectralRadiusUpperTail
