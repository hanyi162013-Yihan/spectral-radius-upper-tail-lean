import SpectralRadiusUpperTail.RegressionMatrixConvergence
import SpectralRadiusUpperTail.SecondMomentProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

/-- Actual real regression matrices vanish in Frobenius probability, on the
actual tilted matrix laws, with arbitrary vanishing coefficient envelopes. -/
theorem real_gaussianRegressionMatrix_probability_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (N : ℕ → ℕ) (hN : ∀ᶠ n in atTop, 0 < N n)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin (N n), ‖v n j.val‖^2) ≤ 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hflat : ∀ n, ∀ j : Fin (N n), ‖v n j.val‖ ≤ δ n)
    (t : (n : ℕ) → Fin (N n) → ℝ) (ht : ∀ n i, ‖t n i‖ ≤ K) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)).real
      {x | r ≤ ‖gaussianRegressionMatrix μ (2*η) (v n) (t n) η x‖}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  have (n : ℕ) : IsProbabilityMeasure (gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)) :=
    gaussianTiltedMatrixLaw_probability μ hX hm hvar (v n) (hv n) (2*η) (by positivity) (t n)
  obtain ⟨hi, hm'⟩ := real_gaussianRegressionMatrix_tendsto μ hm hvar d hd hexp η K hη
    N hN v hv δ hδ hflat t ht
  exact norm_probability_tendsto_of_secondMoment _ _ _ _ hi hm' r hr

/-- Proper-complex actual regression matrices vanish in Frobenius probability. -/
theorem complex_gaussianRegressionMatrix_probability_tendsto (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (N : ℕ → ℕ) (hN : ∀ᶠ n in atTop, 0 < N n)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin (N n), ‖v n j.val‖^2) ≤ 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hflat : ∀ n, ∀ j : Fin (N n), ‖v n j.val‖ ≤ δ n)
    (t : (n : ℕ) → Fin (N n) → ℂ) (ht : ∀ n i, ‖t n i‖ ≤ K) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ η (v n) (t n)).real
      {x | r ≤ ‖gaussianRegressionMatrix μ η (v n) (t n) η x‖}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  have (n : ℕ) : IsProbabilityMeasure (gaussianTiltedMatrixLaw μ η (v n) (t n)) :=
    gaussianTiltedMatrixLaw_probability μ hX hm hvar (v n) (hv n) η hη (t n)
  obtain ⟨hi, hm'⟩ := complex_gaussianRegressionMatrix_tendsto μ hm hvar hpseudo d hd hexp η K hη
    N hN v hv δ hδ hflat t ht
  exact norm_probability_tendsto_of_secondMoment _ _ _ _ hi hm' r hr

lemma flat_coefficient_scale_tendsto (L : ℝ) :
    Tendsto (fun n : ℕ => L/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- The n-by-n flat regime used in the matrix lower-bound construction. -/
theorem real_flat_regressionMatrix_probability_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℝ) (ht : ∀ n i, ‖t n i‖ ≤ K) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)).real
      {x | r ≤ ‖gaussianRegressionMatrix μ (2*η) (v n) (t n) η x‖}) atTop (𝓝 0) :=
  real_gaussianRegressionMatrix_probability_tendsto μ hm hvar d hd hexp η K hη
    (fun n => n) (eventually_gt_atTop 0) v hv _ (flat_coefficient_scale_tendsto L) hflat t ht r hr

/-- The corresponding flat proper-complex matrix remainder. -/
theorem complex_flat_regressionMatrix_probability_tendsto (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℂ) (ht : ∀ n i, ‖t n i‖ ≤ K) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ η (v n) (t n)).real
      {x | r ≤ ‖gaussianRegressionMatrix μ η (v n) (t n) η x‖}) atTop (𝓝 0) :=
  complex_gaussianRegressionMatrix_probability_tendsto μ hm hvar hpseudo d hd hexp η K hη
    (fun n => n) (eventually_gt_atTop 0) v hv _ (flat_coefficient_scale_tendsto L) hflat t ht r hr

#print axioms real_flat_regressionMatrix_probability_tendsto
#print axioms complex_flat_regressionMatrix_probability_tendsto
end SpectralRadiusUpperTail
