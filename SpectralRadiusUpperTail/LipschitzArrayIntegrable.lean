import SpectralRadiusUpperTail.ProductDiscardedEnergy
import SpectralRadiusUpperTail.ArrayTruncationEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped BigOperators NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

lemma discardedSquare_zero (x : 𝕂) : discardedSquare 0 x = ‖x‖^2 := by
  by_cases hx : 0 < ‖x‖
  · simp [discardedSquare, hx]
  · have he : ‖x‖ = 0 := le_antisymm (le_of_not_gt hx) (norm_nonneg _)
    simp [discardedSquare, he]

lemma iid_euclidean_norm_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ)
    (h2 : Integrable (fun x : 𝕂 => ‖x‖^2) μ) :
    Integrable (fun x : Fin N → 𝕂 => ‖toLp 2 x‖) (Measure.pi (fun _ => μ)) := by
  have he (x : Fin N → 𝕂) : Real.sqrt (∑ i, discardedSquare 0 (x i)) = ‖toLp 2 x‖ := by
    simp_rw [discardedSquare_zero]
    rw [← EuclideanSpace.norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [he] using (product_discarded_energy_sqrt μ N 0 h2).1

lemma lipschitz_iid_array_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ)
    (h2 : Integrable (fun x : 𝕂 => ‖x‖^2) μ)
    (C : ℝ≥0) (f : EuclideanSpace 𝕂 (Fin N) → ℝ) (hf : LipschitzWith C f) :
    Integrable (fun x : Fin N → 𝕂 => f (toLp 2 x)) (Measure.pi (fun _ => μ)) := by
  letI : MeasurableSpace (EuclideanSpace 𝕂 (Fin N)) := borel _
  letI : BorelSpace (EuclideanSpace 𝕂 (Fin N)) := ⟨rfl⟩
  have hm : Measurable (fun x : Fin N → 𝕂 => f (toLp 2 x)) :=
    hf.continuous.measurable.comp (PiLp.continuous_toLp 2 (fun _ : Fin N => 𝕂)).measurable
  apply ((integrable_const ‖f 0‖).add ((iid_euclidean_norm_integrable μ N h2).const_mul (C : ℝ))).mono'
    hm.aestronglyMeasurable
  filter_upwards [] with x
  have hh := hf.norm_sub_le (toLp 2 x) 0
  simp only [sub_zero] at hh
  have ht := norm_add_le (f (toLp 2 x)-f 0) (f 0)
  rw [sub_add_cancel] at ht
  change ‖f (toLp 2 x)‖ ≤ ‖f 0‖+(C : ℝ)*‖toLp 2 x‖
  linarith only [hh, ht]

#print axioms discardedSquare_zero
#print axioms iid_euclidean_norm_integrable
#print axioms lipschitz_iid_array_integrable
end SpectralRadiusUpperTail
