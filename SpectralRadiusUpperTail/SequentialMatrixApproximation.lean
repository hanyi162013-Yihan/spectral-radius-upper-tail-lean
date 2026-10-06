import SpectralRadiusUpperTail.SequentialTotalError
import SpectralRadiusUpperTail.DescendingOperatorBound
import SpectralRadiusUpperTail.NormProbabilityProduct
import SpectralRadiusUpperTail.ActualApproximationIdentity

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology

/-- Actual tilted-to-iid triangular approximation on the fixed coupling. -/
theorem real_sequential_matrix_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℝ) (ht : ∀ n i, ‖t n i‖ ≤ K)
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) (2*η) (t n)).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (normalizedArray (fun i => coordinateVector Prod.fst n (x i)) -
          (normalizedArray (fun i => comparatorVector n (x i)) *
            descendingTriangularInverse η (fun j : Fin n => v n j.val) +
            gaussianMeanMatrix (v n) (t n) η))‖}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) (2*η) (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) (2*η) (by positivity) (t n)
  have htot := real_sequential_total_error μ hm hvar d hd hexp η K L hη hL
    v hv hflat t ht
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (descendingTriangularInverse η (fun j : Fin n => v n j.val))‖ ≤
        1+Real.sqrt (1/(2*η^2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact descendingTriangularInverse_operator_bound η hη _ (hunit n (by omega))
  have hprod := norm_probability_mul_bounded_tendsto
    (fun n => Fin n → Fin n → ℝ × ℝ)
    (fun n => EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (fun n => gaussianSequentialMatrixLaw μ (v n) (2*η) (t n))
    (fun n x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (gaussianCenteredMatrix μ (2*η) (v n) (t n)
        (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i)) +
       gaussianRegressionMatrix μ (2*η) (v n) (t n) η
        (fun i => coordinateVector Prod.fst n (x i))))
    (fun n => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (descendingTriangularInverse η (fun j : Fin n => v n j.val)))
    htot (1+Real.sqrt (1/(2*η^2))) (by positivity) hb r hr
  convert hprod using 1
  funext n
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [gaussianMatrix_approximation_error μ (2*η) (v n) (t n) η hη, map_mul]

/-- Actual tilted-to-iid triangular approximation on the fixed coupling. -/
theorem complex_sequential_matrix_approximation (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℂ) (ht : ∀ n i, ‖t n i‖ ≤ K)
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) η (t n)).real
      {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        (normalizedArray (fun i => coordinateVector Prod.fst n (x i)) -
          (normalizedArray (fun i => comparatorVector n (x i)) *
            descendingTriangularInverse η (fun j : Fin n => v n j.val) +
            gaussianMeanMatrix (v n) (t n) η))‖}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) η (t n)) :=
    gaussianSequentialMatrixLaw_probability μ (v n) η hη (t n)
  have htot := complex_sequential_total_error μ hm hvar hpseudo d hd hexp η K L hη hL
    v hv hflat t ht
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        (descendingTriangularInverse η (fun j : Fin n => v n j.val))‖ ≤
        1+Real.sqrt (1/(2*η^2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact descendingTriangularInverse_operator_bound η hη _ (hunit n (by omega))
  have hprod := norm_probability_mul_bounded_tendsto
    (fun n => Fin n → Fin n → ℂ × ℂ)
    (fun n => EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (fun n => gaussianSequentialMatrixLaw μ (v n) η (t n))
    (fun n x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      (gaussianCenteredMatrix μ η (v n) (t n)
        (fun i => coordinateVector Prod.fst n (x i)) (fun i => comparatorVector n (x i)) +
       gaussianRegressionMatrix μ η (v n) (t n) η
        (fun i => coordinateVector Prod.fst n (x i))))
    (fun n => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      (descendingTriangularInverse η (fun j : Fin n => v n j.val)))
    htot (1+Real.sqrt (1/(2*η^2))) (by positivity) hb r hr
  convert hprod using 1
  funext n
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [gaussianMatrix_approximation_error μ η (v n) (t n) η hη, map_mul]

#print axioms real_sequential_matrix_approximation
#print axioms complex_sequential_matrix_approximation
end SpectralRadiusUpperTail
