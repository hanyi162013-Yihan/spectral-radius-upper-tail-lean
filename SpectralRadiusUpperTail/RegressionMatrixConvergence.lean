import SpectralRadiusUpperTail.UniformRegressionMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Uniform coefficient control implies convergence for varying dimensions,
coefficient vectors and row targets, on their actual matrix probability spaces. -/
theorem gaussianRegressionMatrix_tendsto_of_uniform (μ : Measure 𝕂) (a η K : ℝ)
    (huniform : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 0 < N → ∀ v : ℕ → 𝕂,
      (∑ j : Fin N, ‖v j.val‖^2) ≤ 1 → (∀ j : Fin N, ‖v j.val‖ ≤ δ) →
      ∀ t : Fin N → 𝕂, (∀ i, ‖t i‖ ≤ K) →
      Integrable (fun x => ‖gaussianRegressionMatrix μ a v t η x‖^2) (gaussianTiltedMatrixLaw μ a v t) ∧
      (∫ x, ‖gaussianRegressionMatrix μ a v t η x‖^2 ∂gaussianTiltedMatrixLaw μ a v t) < ε)
    (N : ℕ → ℕ) (hN : ∀ᶠ n in atTop, 0 < N n) (v : ℕ → ℕ → 𝕂)
    (hv : ∀ n, (∑ j : Fin (N n), ‖v n j.val‖^2) ≤ 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hflat : ∀ n, ∀ j : Fin (N n), ‖v n j.val‖ ≤ δ n)
    (t : (n : ℕ) → Fin (N n) → 𝕂) (ht : ∀ n i, ‖t n i‖ ≤ K) :
    (∀ᶠ n in atTop, Integrable (fun x => ‖gaussianRegressionMatrix μ a (v n) (t n) η x‖^2)
      (gaussianTiltedMatrixLaw μ a (v n) (t n))) ∧
    Tendsto (fun n => ∫ x, ‖gaussianRegressionMatrix μ a (v n) (t n) η x‖^2
      ∂gaussianTiltedMatrixLaw μ a (v n) (t n)) atTop (𝓝 0) := by
  have he (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop,
      Integrable (fun x => ‖gaussianRegressionMatrix μ a (v n) (t n) η x‖^2)
        (gaussianTiltedMatrixLaw μ a (v n) (t n)) ∧
      (∫ x, ‖gaussianRegressionMatrix μ a (v n) (t n) η x‖^2
        ∂gaussianTiltedMatrixLaw μ a (v n) (t n)) < ε := by
    obtain ⟨κ, hκ, hκ'⟩ := huniform ε hε
    have hδ' := hδ.eventually (Iio_mem_nhds hκ)
    filter_upwards [hN, hδ'] with n hn hdn
    exact hκ' (N n) hn (v n) (hv n) (fun j => (hflat n j).trans hdn.le) (t n) (ht n)
  refine ⟨(he 1 (by norm_num)).mono (fun _ h => h.1), tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro r hr
    exact Eventually.of_forall (fun n => hr.trans_le (integral_nonneg (fun _ => sq_nonneg _)))
  · intro ε hε
    exact (he ε hε).mono (fun _ h => h.2)

/-- Actual real normalized regression matrices converge to zero in squared
Frobenius mean whenever the maximal coefficients vanish. -/
theorem real_gaussianRegressionMatrix_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (N : ℕ → ℕ) (hN : ∀ᶠ n in atTop, 0 < N n)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin (N n), ‖v n j.val‖^2) ≤ 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hflat : ∀ n, ∀ j : Fin (N n), ‖v n j.val‖ ≤ δ n)
    (t : (n : ℕ) → Fin (N n) → ℝ) (ht : ∀ n i, ‖t n i‖ ≤ K) :
    (∀ᶠ n in atTop, Integrable (fun x => ‖gaussianRegressionMatrix μ (2*η) (v n) (t n) η x‖^2)
      (gaussianTiltedMatrixLaw μ (2*η) (v n) (t n))) ∧
    Tendsto (fun n => ∫ x, ‖gaussianRegressionMatrix μ (2*η) (v n) (t n) η x‖^2
      ∂gaussianTiltedMatrixLaw μ (2*η) (v n) (t n)) atTop (𝓝 0) :=
  gaussianRegressionMatrix_tendsto_of_uniform μ (2*η) η K
    (real_gaussianRegressionMatrix_uniform μ hm hvar d hd hexp η K hη) N hN v hv δ hδ hflat t ht

/-- Actual proper-complex normalized regression matrices obey the same
squared-mean convergence, with no coordinate-independence assumption. -/
theorem complex_gaussianRegressionMatrix_tendsto (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (N : ℕ → ℕ) (hN : ∀ᶠ n in atTop, 0 < N n)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin (N n), ‖v n j.val‖^2) ≤ 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hflat : ∀ n, ∀ j : Fin (N n), ‖v n j.val‖ ≤ δ n)
    (t : (n : ℕ) → Fin (N n) → ℂ) (ht : ∀ n i, ‖t n i‖ ≤ K) :
    (∀ᶠ n in atTop, Integrable (fun x => ‖gaussianRegressionMatrix μ η (v n) (t n) η x‖^2)
      (gaussianTiltedMatrixLaw μ η (v n) (t n))) ∧
    Tendsto (fun n => ∫ x, ‖gaussianRegressionMatrix μ η (v n) (t n) η x‖^2
      ∂gaussianTiltedMatrixLaw μ η (v n) (t n)) atTop (𝓝 0) :=
  gaussianRegressionMatrix_tendsto_of_uniform μ η η K
    (complex_gaussianRegressionMatrix_uniform μ hm hvar hpseudo d hd hexp η K hη) N hN v hv δ hδ hflat t ht

#print axioms real_gaussianRegressionMatrix_tendsto
#print axioms complex_gaussianRegressionMatrix_tendsto
end SpectralRadiusUpperTail
