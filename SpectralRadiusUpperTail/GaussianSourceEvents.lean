import SpectralRadiusUpperTail.SpectralMeasurable
import SpectralRadiusUpperTail.GaussianComparatorEntries

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ}

lemma measurable_normalizedArray :
    Measurable (normalizedArray (N := n) (𝕂 := 𝕂)) := by
  unfold normalizedArray
  fun_prop

lemma gaussian_source_event_probability_eq (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂)
    (hv : ∑ j : Fin n, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : Fin n → 𝕂)
    (P : Matrix (Fin n) (Fin n) 𝕂 → Prop) (hP : MeasurableSet {A | P A}) :
    (gaussianTiltedMatrixLaw μ a v t).real {x | P (normalizedArray x)} =
      (gaussianSequentialMatrixLaw μ v a t).real
        {x | P (normalizedArray (fun i => coordinateVector Prod.fst n (x i)))} := by
  have hf : Measurable (fun x : Fin n → Fin n → 𝕂 × 𝕂 =>
      fun i => coordinateVector Prod.fst n (x i)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_coordinateVector (@Prod.fst 𝕂 𝕂) measurable_fst n).comp (measurable_pi_apply i))
  rw [← gaussianSequentialMatrixLaw_source μ hX hm hvar v hv a ha t]
  exact map_measureReal_apply hf (hP.preimage measurable_normalizedArray)

#print axioms measurable_normalizedArray
#print axioms gaussian_source_event_probability_eq
end SpectralRadiusUpperTail
