import SpectralRadiusUpperTail.GaussianRegressionMatrix
import SpectralRadiusUpperTail.UniformRowRegression

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- Uniform actual row control bounds the actual normalized matrix error. -/
lemma gaussianRegressionMatrix_bound_of_rows (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (hN : 0 < N) (a : ℝ) (ha : 0 < a)
    (t : Fin N → 𝕂) (η ε : ℝ)
    (hrow : ∀ i : Fin N,
      Integrable (fun x => ∑ j : Fin N, ‖gaussianRowRegression μ a v j (t i) η x‖^2)
        (gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i)) ∧
      (∫ x, ∑ j : Fin N, ‖gaussianRowRegression μ a v j (t i) η x‖^2
        ∂gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) (t i)) < ε) :
    Integrable (fun x => ‖gaussianRegressionMatrix μ a v t η x‖^2) (gaussianTiltedMatrixLaw μ a v t) ∧
      (∫ x, ‖gaussianRegressionMatrix μ a v t η x‖^2 ∂gaussianTiltedMatrixLaw μ a v t) ≤ ε := by
  obtain ⟨hi, heq⟩ := gaussianRegressionMatrix_secondMoment μ hX hm hvar v hv a ha t η (fun i => (hrow i).1)
  refine ⟨hi, ?_⟩
  rw [heq]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  calc
    _ ≤ (1/(N : ℝ))*(∑ _i : Fin N, ε) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hrow i).2.le)) (by positivity)
    _ = ε := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

/-- A single coefficient cutoff controls the full actual real error matrix,
uniformly over dimension and bounded row targets. -/
theorem real_gaussianRegressionMatrix_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℝ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N → ∀ v : ℕ → ℝ,
      (∑ j : Fin N, ‖v j.val‖^2) ≤ 1 → (∀ j : Fin N, ‖v j.val‖ ≤ δ) →
      ∀ t : Fin N → ℝ, (∀ i, ‖t i‖ ≤ K) →
      Integrable (fun x => ‖gaussianRegressionMatrix μ (2*η) v t η x‖^2) (gaussianTiltedMatrixLaw μ (2*η) v t) ∧
      (∫ x, ‖gaussianRegressionMatrix μ (2*η) v t η x‖^2 ∂gaussianTiltedMatrixLaw μ (2*η) v t) < ε := by
  obtain ⟨δ, hδ, hrow⟩ := real_gaussianRowRegression_uniform μ hm hvar d hd hexp η K hη (ε/2) (by positivity)
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  refine ⟨δ, hδ, ?_⟩
  intro N hN v hv hflat t ht
  obtain ⟨hi, hb⟩ := gaussianRegressionMatrix_bound_of_rows μ hX hm hvar v hv hN (2*η)
    (by positivity) t η (ε/2) (fun i => hrow N v hv hflat (t i) (ht i))
  exact ⟨hi, hb.trans_lt (by linarith)⟩

/-- The same actual matrix-error modulus for proper complex entries. -/
theorem complex_gaussianRegressionMatrix_uniform (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : ℂ => Real.exp (4*d*‖x‖^2)) μ)
    (η K : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N → ∀ v : ℕ → ℂ,
      (∑ j : Fin N, ‖v j.val‖^2) ≤ 1 → (∀ j : Fin N, ‖v j.val‖ ≤ δ) →
      ∀ t : Fin N → ℂ, (∀ i, ‖t i‖ ≤ K) →
      Integrable (fun x => ‖gaussianRegressionMatrix μ η v t η x‖^2) (gaussianTiltedMatrixLaw μ η v t) ∧
      (∫ x, ‖gaussianRegressionMatrix μ η v t η x‖^2 ∂gaussianTiltedMatrixLaw μ η v t) < ε := by
  obtain ⟨δ, hδ, hrow⟩ := complex_gaussianRowRegression_uniform μ hm hvar hpseudo d hd hexp η K hη
    (ε/2) (by positivity)
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 2)
  refine ⟨δ, hδ, ?_⟩
  intro N hN v hv hflat t ht
  obtain ⟨hi, hb⟩ := gaussianRegressionMatrix_bound_of_rows μ hX hm hvar v hv hN η hη t η (ε/2)
    (fun i => hrow N v hv hflat (t i) (ht i))
  exact ⟨hi, hb.trans_lt (by linarith)⟩

#print axioms real_gaussianRegressionMatrix_uniform
#print axioms complex_gaussianRegressionMatrix_uniform
end SpectralRadiusUpperTail
