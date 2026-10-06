import SpectralRadiusUpperTail.ProductProjectionMGF
import SpectralRadiusUpperTail.RowNormalizerBound

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 ι : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] [Fintype ι]

/-- Both real and imaginary projections of actual iid finite sums inherit one
MGF constant, depending only on the entry law and its square-exponential moment. -/
theorem iid_row_projection_mgf (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ι → 𝕂) (hXi : Integrable (fun x : 𝕂 => x) μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ)
    (π : 𝕂 →L[ℝ] ℝ) (hπ : ∀ x, |π x| ≤ ‖x‖) (t : ℝ) :
    Integrable (fun s : ι → 𝕂 => Real.exp (t*π (∑ i, v i*s i)))
      (Measure.pi (fun _ : ι => μ)) ∧
      (∫ s, Real.exp (t*π (∑ i, v i*s i)) ∂Measure.pi (fun _ : ι => μ)) ≤
        Real.exp (squareExpMgfConstant τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)*t^2) := by
  have hmeas (i : ι) : Measurable (fun x : 𝕂 => π (v i*x)) :=
    (π.continuous.comp (continuous_const.mul continuous_id)).measurable
  have hbound (i : ι) (x : 𝕂) : |π (v i*x)| ≤ ‖v i‖*‖x‖ := by
    simpa only [norm_mul] using hπ (v i*x)
  have hi (i : ι) : Integrable (fun x : 𝕂 => π (v i*x)) μ := by
    apply (hXi.norm.const_mul ‖v i‖).mono' (hmeas i).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound i x)
  have hmean (i : ι) : (∫ x : 𝕂, π (v i*x) ∂μ) = 0 := by
    rw [π.integral_comp_comm (hXi.const_mul (v i)), integral_const_mul, hm, mul_zero, map_zero]
  have hh := product_projection_mgf μ (fun i x => π (v i*x)) hmeas hi hmean
    (fun i => ‖v i‖) (fun i => norm_nonneg _) hbound hv τ hτ hexp t
  simpa only [map_sum] using hh

#print axioms iid_row_projection_mgf
end SpectralRadiusUpperTail
