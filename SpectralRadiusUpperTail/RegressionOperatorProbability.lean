import SpectralRadiusUpperTail.RegressionMatrixProbability
import SpectralRadiusUpperTail.MatrixOperatorComparison

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

/-- The actual normalized real regression remainder vanishes in Euclidean
operator norm in the flat regime used by the lower-bound construction. -/
theorem real_flat_regressionMatrix_operator_probability_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℝ) (ht : ∀ n i, ‖t n i‖ ≤ K) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (gaussianRegressionMatrix μ (2*η) (v n) (t n) η x)‖}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  have (n : ℕ) : IsProbabilityMeasure (gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)) :=
    gaussianTiltedMatrixLaw_probability μ hX hm hvar (v n) (hv n) (2*η) (by positivity) (t n)
  exact operator_probability_tendsto_of_frobenius _ _ (fun n => n)
    (fun n => gaussianRegressionMatrix μ (2*η) (v n) (t n) η) r
    (real_flat_regressionMatrix_probability_tendsto μ hm hvar d hd hexp η K L hη v hv hflat t ht r hr)

/-- The same actual Euclidean operator-norm conclusion for proper complex entries. -/
theorem complex_flat_regressionMatrix_operator_probability_tendsto (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℂ) (ht : ∀ n i, ‖t n i‖ ≤ K) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ η (v n) (t n)).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        (gaussianRegressionMatrix μ η (v n) (t n) η x)‖}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  have (n : ℕ) : IsProbabilityMeasure (gaussianTiltedMatrixLaw μ η (v n) (t n)) :=
    gaussianTiltedMatrixLaw_probability μ hX hm hvar (v n) (hv n) η hη (t n)
  exact operator_probability_tendsto_of_frobenius _ _ (fun n => n)
    (fun n => gaussianRegressionMatrix μ η (v n) (t n) η) r
    (complex_flat_regressionMatrix_probability_tendsto μ hm hvar hpseudo d hd hexp η K L hη v hv hflat t ht r hr)

#print axioms real_flat_regressionMatrix_operator_probability_tendsto
#print axioms complex_flat_regressionMatrix_operator_probability_tendsto
end SpectralRadiusUpperTail
