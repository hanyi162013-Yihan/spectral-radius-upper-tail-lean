import SpectralRadiusUpperTail.ComplexRegularizedEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma iid_complexRegularizedLogDet_secondMoment (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h4 : Integrable (fun z : ℂ => ‖z‖^4) μ) (n : ℕ) (hn : 0 < n)
    (z : ℂ) (s R : ℝ) (hs : 0 < s) (hz : ‖z‖ ≤ R) :
    Integrable (fun x : Fin n × Fin n → ℂ =>
      (complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ))^2)
      (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin n × Fin n → ℂ, (complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ))^2
      ∂Measure.pi (fun _ => μ)) ≤
        2*(|Real.log s|+2*R^2+s)^2+8*(∫ z : ℂ, ‖z‖^4 ∂μ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hp := iid_averageEntryEnergy_secondMoment (ι := Fin n × Fin n) μ h4
  have hdom := (integrable_const (2*(|Real.log s|+2*R^2+s)^2)).add (hp.1.const_mul 8)
  have hm : Measurable (fun x : Fin n × Fin n → ℂ =>
      (complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ))^2) :=
    (((complexRegularizedLogDet_measurable n z s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _).pow_const _
  have hi : Integrable (fun x : Fin n × Fin n → ℂ =>
      (complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ))^2) (Measure.pi (fun _ => μ)) := by
    apply hdom.mono' hm.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact normalized_complexRegularizedLogDet_sq_bound hn x z s R hs hz
  refine ⟨hi, (integral_mono hi hdom (fun x => normalized_complexRegularizedLogDet_sq_bound hn x z s R hs hz)).trans ?_⟩
  change (∫ x : Fin n × Fin n → ℂ, 2*(|Real.log s|+2*R^2+s)^2+8*averageEntryEnergy x^2
    ∂Measure.pi (fun _ => μ)) ≤ _
  rw [integral_add (integrable_const _) (hp.1.const_mul 8), integral_const, integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  linarith [hp.2]

lemma iid_complexRegularizedLogDet_integrable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h4 : Integrable (fun z : ℂ => ‖z‖^4) μ) (n : ℕ) (hn : 0 < n)
    (z : ℂ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Fin n × Fin n → ℂ => complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ))
      (Measure.pi (fun _ => μ)) := by
  have hp := (iid_complexRegularizedLogDet_secondMoment μ h4 n hn z s ‖z‖ hs le_rfl).1
  have hm : AEStronglyMeasurable (fun x : Fin n × Fin n → ℂ =>
      complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ)) (Measure.pi (fun _ => μ)) :=
    (((complexRegularizedLogDet_measurable n z s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _).aestronglyMeasurable
  have h2 : Integrable (fun x : Fin n × Fin n → ℂ =>
      ‖complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ)‖^2) (Measure.pi (fun _ => μ)) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hp
  exact ((memLp_two_iff_integrable_sq_norm hm).mpr h2).integrable (by norm_num)

#print axioms iid_complexRegularizedLogDet_integrable
#print axioms iid_complexRegularizedLogDet_secondMoment
end SpectralRadiusUpperTail
