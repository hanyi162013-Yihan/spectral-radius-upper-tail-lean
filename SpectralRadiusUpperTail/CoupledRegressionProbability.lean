import SpectralRadiusUpperTail.GaussianRegressionTransfer
import SpectralRadiusUpperTail.RegressionOperatorProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

/-- Actual coupled real arrays have both prescribed full marginals and a
regression remainder vanishing in Euclidean operator probability. -/
theorem real_coupled_regression_remainder_exists (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℝ) (ht : ∀ n i, ‖t n i‖ ≤ K) :
    ∃ Γ : (n : ℕ) → Measure (Fin n → Fin n → ℝ × ℝ),
      (∀ n, IsProbabilityMeasure (Γ n)) ∧
      (∀ n, (Γ n).map (fun x i => coordinateVector Prod.fst n (x i)) =
        gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)) ∧
      (∀ n, (Γ n).map (fun x i => comparatorVector n (x i)) =
        Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) ∧
      ∀ r : ℝ, 0 < r → Tendsto (fun n => (Γ n).real
        {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (gaussianRegressionMatrix μ (2*η) (v n) (t n) η
            (fun i => coordinateVector Prod.fst n (x i)))‖}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  choose Γ hΓ hsource hcomparator using (fun n => gaussianTiltedMatrix_coupling_exists μ hX hm hvar
    (v n) (hv n) (2*η) (by positivity) (t n))
  have (n : ℕ) : IsProbabilityMeasure (Γ n) := hΓ n
  refine ⟨Γ, hΓ, hsource, hcomparator, ?_⟩
  intro r hr
  apply operator_probability_tendsto_of_frobenius _ Γ (fun n => n)
    (fun n x => gaussianRegressionMatrix μ (2*η) (v n) (t n) η
      (fun i => coordinateVector Prod.fst n (x i))) r
  have he : (fun n => (Γ n).real {x | r ≤ ‖gaussianRegressionMatrix μ (2*η) (v n) (t n) η
      (fun i => coordinateVector Prod.fst n (x i))‖}) =
      (fun n => (gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)).real
        {x | r ≤ ‖gaussianRegressionMatrix μ (2*η) (v n) (t n) η x‖}) := by
    funext n
    exact gaussianRegressionMatrix_source_probability μ hX hm hvar (v n) (hv n) (2*η)
      (by positivity) (t n) η r hr.le (Γ n) (hsource n)
  rw [he]
  exact real_flat_regressionMatrix_probability_tendsto μ hm hvar d hd hexp η K L hη v hv hflat t ht r hr

/-- The coupled proper-complex arrays satisfy the same actual operator-norm
regression conclusion without component-independence assumptions. -/
theorem complex_coupled_regression_remainder_exists (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K L : ℝ) (hη : 0 < η)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → ℂ) (ht : ∀ n i, ‖t n i‖ ≤ K) :
    ∃ Γ : (n : ℕ) → Measure (Fin n → Fin n → ℂ × ℂ),
      (∀ n, IsProbabilityMeasure (Γ n)) ∧
      (∀ n, (Γ n).map (fun x i => coordinateVector Prod.fst n (x i)) =
        gaussianTiltedMatrixLaw μ η (v n) (t n)) ∧
      (∀ n, (Γ n).map (fun x i => comparatorVector n (x i)) =
        Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) ∧
      ∀ r : ℝ, 0 < r → Tendsto (fun n => (Γ n).real
        {x | r ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
          (gaussianRegressionMatrix μ η (v n) (t n) η
            (fun i => coordinateVector Prod.fst n (x i)))‖}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  choose Γ hΓ hsource hcomparator using (fun n => gaussianTiltedMatrix_coupling_exists μ hX hm hvar
    (v n) (hv n) η hη (t n))
  have (n : ℕ) : IsProbabilityMeasure (Γ n) := hΓ n
  refine ⟨Γ, hΓ, hsource, hcomparator, ?_⟩
  intro r hr
  apply operator_probability_tendsto_of_frobenius _ Γ (fun n => n)
    (fun n x => gaussianRegressionMatrix μ η (v n) (t n) η
      (fun i => coordinateVector Prod.fst n (x i))) r
  have he : (fun n => (Γ n).real {x | r ≤ ‖gaussianRegressionMatrix μ η (v n) (t n) η
      (fun i => coordinateVector Prod.fst n (x i))‖}) =
      (fun n => (gaussianTiltedMatrixLaw μ η (v n) (t n)).real
        {x | r ≤ ‖gaussianRegressionMatrix μ η (v n) (t n) η x‖}) := by
    funext n
    exact gaussianRegressionMatrix_source_probability μ hX hm hvar (v n) (hv n) η hη (t n) η r hr.le
      (Γ n) (hsource n)
  rw [he]
  exact complex_flat_regressionMatrix_probability_tendsto μ hm hvar hpseudo d hd hexp η K L hη v hv hflat t ht r hr

#print axioms real_coupled_regression_remainder_exists
#print axioms complex_coupled_regression_remainder_exists
end SpectralRadiusUpperTail
