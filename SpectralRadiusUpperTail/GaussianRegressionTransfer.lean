import SpectralRadiusUpperTail.GaussianMatrixCoupling

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

lemma gaussianRegressionMatrix_norm_sq_measurable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) (η : ℝ) :
    Measurable (fun x => ‖gaussianRegressionMatrix μ a v t η x‖^2) := by
  simp_rw [gaussianRegressionMatrix_norm_sq]
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((gaussianRowRegression_continuous μ hX hm hvar a ha v hv j (t i) η).measurable.comp
    (measurable_pi_apply i)).norm.pow_const 2

lemma gaussianRegressionMatrix_norm_event_measurable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) (η r : ℝ)
    (hr : 0 ≤ r) : MeasurableSet {x | r ≤ ‖gaussianRegressionMatrix μ a v t η x‖} := by
  have he : {x | r ≤ ‖gaussianRegressionMatrix μ a v t η x‖} =
      {x | r^2 ≤ ‖gaussianRegressionMatrix μ a v t η x‖^2} := by
    ext x
    exact (sq_le_sq₀ hr (norm_nonneg _)).symm
  rw [he]
  exact measurableSet_le measurable_const
    (gaussianRegressionMatrix_norm_sq_measurable μ hX hm hvar v hv a ha t η)

/-- Any coupling with the proved source marginal has exactly the same actual
regression second moment; no independence is needed for this transfer. -/
theorem gaussianRegressionMatrix_source_integral (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) (η : ℝ)
    (Γ : Measure (Fin N → Fin N → 𝕂 × 𝕂))
    (hsource : Γ.map (fun x i => coordinateVector Prod.fst N (x i)) = gaussianTiltedMatrixLaw μ a v t) :
    (∫ x, ‖gaussianRegressionMatrix μ a v t η (fun i => coordinateVector Prod.fst N (x i))‖^2 ∂Γ) =
      ∫ x, ‖gaussianRegressionMatrix μ a v t η x‖^2 ∂gaussianTiltedMatrixLaw μ a v t := by
  have hf : Measurable (fun (x : Fin N → Fin N → 𝕂 × 𝕂) i => coordinateVector (@Prod.fst 𝕂 𝕂) N (x i)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_coordinateVector Prod.fst measurable_fst N).comp (measurable_pi_apply i))
  have hh := integral_map (μ := Γ) hf.aemeasurable
    (gaussianRegressionMatrix_norm_sq_measurable μ hX hm hvar v hv a ha t η).aestronglyMeasurable
  rw [hsource] at hh
  exact hh.symm

/-- Equality of the actual error tail probabilities under the coupling and
under its actual tilted matrix source. -/
theorem gaussianRegressionMatrix_source_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂) (η r : ℝ)
    (hr : 0 ≤ r) (Γ : Measure (Fin N → Fin N → 𝕂 × 𝕂))
    (hsource : Γ.map (fun x i => coordinateVector Prod.fst N (x i)) = gaussianTiltedMatrixLaw μ a v t) :
    Γ.real {x | r ≤ ‖gaussianRegressionMatrix μ a v t η (fun i => coordinateVector Prod.fst N (x i))‖} =
      (gaussianTiltedMatrixLaw μ a v t).real {x | r ≤ ‖gaussianRegressionMatrix μ a v t η x‖} := by
  have hf : Measurable (fun (x : Fin N → Fin N → 𝕂 × 𝕂) i => coordinateVector (@Prod.fst 𝕂 𝕂) N (x i)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_coordinateVector Prod.fst measurable_fst N).comp (measurable_pi_apply i))
  rw [← hsource]
  change (Γ _).toReal = ((Γ.map _) _).toReal
  rw [Measure.map_apply hf (gaussianRegressionMatrix_norm_event_measurable μ hX hm hvar v hv a ha t η r hr)]
  rfl

#print axioms gaussianRegressionMatrix_source_integral
#print axioms gaussianRegressionMatrix_source_probability
end SpectralRadiusUpperTail
