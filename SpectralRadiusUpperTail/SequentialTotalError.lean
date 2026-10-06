import SpectralRadiusUpperTail.GaussianCenteredConvergence
import SpectralRadiusUpperTail.SequentialRegressionProbability
import SpectralRadiusUpperTail.NormProbabilitySum

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

/-- Both actual error terms vanish jointly on the same sequential coupling. -/
theorem real_sequential_total_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℝ) (ht : ∀ n i, ‖t n i‖ ≤ K)
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) (2*η) (t n)).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (gaussianCenteredMatrix μ (2*η) (v n) (t n)
          (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i)) +
          gaussianRegressionMatrix μ (2*η) (v n) (t n) η
          (fun i => coordinateVector Prod.fst n (x i)))‖}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) (2*η) (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) (2*η) (by positivity) (t n)
  have hE := gaussianCenteredMatrix_probability_tendsto μ hm hvar (2*η) d (by positivity) hd hexp
    L K hL v hv hflat t ht
  have hR := real_sequential_regression_remainder μ hm hvar d hd hexp
    η K L hη v hv hflat t ht
  simpa only [map_add] using norm_probability_add_tendsto
    (fun n => Fin n → Fin n → ℝ × ℝ)
    (fun n => EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (fun n => gaussianSequentialMatrixLaw μ (v n) (2*η) (t n))
    (fun n x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (gaussianCenteredMatrix μ (2*η) (v n) (t n)
        (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i))))
    (fun n x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (gaussianRegressionMatrix μ (2*η) (v n) (t n) η
        (fun i => coordinateVector Prod.fst n (x i)))) hE hR r hr

/-- Both actual error terms vanish jointly on the same sequential coupling. -/
theorem complex_sequential_total_error (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℂ) (ht : ∀ n i, ‖t n i‖ ≤ K)
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) η (t n)).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        (gaussianCenteredMatrix μ η (v n) (t n)
          (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i)) +
          gaussianRegressionMatrix μ η (v n) (t n) η
          (fun i => coordinateVector Prod.fst n (x i)))‖}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) η (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) η hη (t n)
  have hE := gaussianCenteredMatrix_probability_tendsto μ hm hvar η d hη hd hexp
    L K hL v hv hflat t ht
  have hR := complex_sequential_regression_remainder μ hm hvar hpseudo d hd hexp
    η K L hη v hv hflat t ht
  simpa only [map_add] using norm_probability_add_tendsto
    (fun n => Fin n → Fin n → ℂ × ℂ)
    (fun n => EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (fun n => gaussianSequentialMatrixLaw μ (v n) η (t n))
    (fun n x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      (gaussianCenteredMatrix μ η (v n) (t n)
        (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i))))
    (fun n x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      (gaussianRegressionMatrix μ η (v n) (t n) η
        (fun i => coordinateVector Prod.fst n (x i)))) hE hR r hr

#print axioms real_sequential_total_error
#print axioms complex_sequential_total_error
end SpectralRadiusUpperTail
