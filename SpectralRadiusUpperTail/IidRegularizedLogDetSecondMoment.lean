import SpectralRadiusUpperTail.NormalizedFrobeniusEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma normalized_regularizedLogDet_sq_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n × Fin n → ℂ) (b s : ℝ) (hs : 0 < s) :
    (matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ))^2 ≤
      2*(|Real.log s|+2*b^2+s)^2+8*averageEntryEnergy x^2 := by
  have hl := normalized_matrixRegularizedLogDet_floor hn (normalizedIidMatrix x) b s hs
  have hu := normalized_regularizedLogDet_energy_bound hn x b s hs
  have hQ := averageEntryEnergy_nonneg x
  let C := |Real.log s|+2*b^2+s
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have habs : |matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)| ≤ C+2*averageEntryEnergy x := by
    rw [abs_le]
    dsimp [C]
    constructor
    · linarith [neg_abs_le (Real.log s), sq_nonneg b]
    · linarith [abs_nonneg (Real.log s)]
  have hsquare := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C+2*averageEntryEnergy x)).mpr habs
  rw [sq_abs] at hsquare
  have hcq := sq_nonneg (C-2*averageEntryEnergy x)
  change _ ≤ 2*C^2+8*averageEntryEnergy x^2
  nlinarith

lemma iid_regularizedLogDet_secondMoment (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h4 : Integrable (fun z : ℂ => ‖z‖^4) μ) (n : ℕ) (hn : 0 < n)
    (b s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Fin n × Fin n → ℂ =>
      (matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ))^2)
      (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin n × Fin n → ℂ, (matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ))^2
      ∂Measure.pi (fun _ => μ)) ≤
        2*(|Real.log s|+2*b^2+s)^2+8*(∫ z : ℂ, ‖z‖^4 ∂μ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hp := iid_averageEntryEnergy_secondMoment (ι := Fin n × Fin n) μ h4
  have hdom := (integrable_const (2*(|Real.log s|+2*b^2+s)^2)).add (hp.1.const_mul 8)
  have hm : Measurable (fun x : Fin n × Fin n → ℂ =>
      (matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ))^2) :=
    (((matrixRegularizedLogDet_measurable n b s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _).pow_const _
  have hi : Integrable (fun x : Fin n × Fin n → ℂ =>
      (matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ))^2) (Measure.pi (fun _ => μ)) := by
    apply hdom.mono' hm.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact normalized_regularizedLogDet_sq_bound hn x b s hs
  refine ⟨hi, (integral_mono hi hdom (fun x => normalized_regularizedLogDet_sq_bound hn x b s hs)).trans ?_⟩
  change (∫ x : Fin n × Fin n → ℂ, 2*(|Real.log s|+2*b^2+s)^2+8*averageEntryEnergy x^2
    ∂Measure.pi (fun _ => μ)) ≤ _
  rw [integral_add (integrable_const _) (hp.1.const_mul 8), integral_const, integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  linarith [hp.2]

#print axioms normalized_regularizedLogDet_sq_bound
#print axioms iid_regularizedLogDet_secondMoment
end SpectralRadiusUpperTail
