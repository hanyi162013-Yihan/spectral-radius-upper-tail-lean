import SpectralRadiusUpperTail.LowerMeanFromProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma integral_upper_of_second_moment (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : Measurable F) (hi : Integrable F μ) (h2 : Integrable (fun x => F x^2) μ)
    (a K : ℝ) (ha : 0 ≤ a) (hK : 0 < K) :
    (∫ x, F x ∂μ) ≤ a+K*μ.real {x | a < F x}+(∫ x, F x^2 ∂μ)/K := by
  let E := {x | a < F x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hF
  have hInd : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const _).indicator hE
  have hpoint (x : Ω) : F x ≤ a+K*E.indicator (fun _ => (1 : ℝ)) x+F x^2/K := by
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx, mul_one]
      have hs := sq_nonneg (F x-K)
      have ht : F x ≤ K+F x^2/K := by
        have hle : F x*K ≤ K^2+F x^2 := by nlinarith [sq_nonneg (F x)]
        have hh := (le_div_iff₀ hK).mpr hle
        convert! hh using 1
        field_simp
        <;> ring
      linarith
    · rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
      have hh : F x ≤ a := le_of_not_gt hx
      exact hh.trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hK.le))
  have hsum : Integrable (fun x => a+K*E.indicator (fun _ => (1 : ℝ)) x) μ :=
    (integrable_const a).add (hInd.const_mul K)
  have hh := integral_mono hi (hsum.add (h2.div_const K)) hpoint
  change (∫ x, F x ∂μ) ≤ ∫ x, a+K*E.indicator (fun _ => (1 : ℝ)) x+F x^2/K ∂μ at hh
  rw [integral_add hsum (h2.div_const K),
    integral_add (integrable_const a) (hInd.const_mul K), integral_const,
    integral_const_mul, integral_indicator_const (1 : ℝ) hE] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one] at hh
  simpa only [div_eq_mul_inv, integral_mul_const] using hh

#print axioms integral_upper_of_second_moment
end SpectralRadiusUpperTail
