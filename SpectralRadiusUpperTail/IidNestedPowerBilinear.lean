import SpectralRadiusUpperTail.IidNormalizedPowerProbability
import SpectralRadiusUpperTail.NormalizedPowerMeasurable
import SpectralRadiusUpperTail.IidMatrixFlatten

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {n k : ℕ}

lemma iidNestedPowerBilinear_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
      {x | ε ≤ ‖∑ i, star (p i) * ((normalizedArray x)^k).mulVec q i‖} ≤
        (pairedMomentConstant μ k/(n : ℝ))/ε^2 := by
  have hb := normalizedPowerBilinear_probability_le μ c hc hexp hm hk hn p q hp hq ε hε
  have hs : MeasurableSet {y | ε ≤ ‖normalizedPowerBilinear p q k y‖} :=
    measurableSet_le measurable_const (measurable_normalizedPowerBilinear p q k).norm
  rw [← iid_matrix_flatten_law μ n] at hb
  change (((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).map
    (fun x : Fin n → Fin n → 𝕂 => fun ij : Fin n × Fin n => x ij.1 ij.2))
      {y | ε ≤ ‖normalizedPowerBilinear p q k y‖}).toReal ≤ _ at hb
  rw [Measure.map_apply (by fun_prop) hs] at hb
  change ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    {x | ε ≤ ‖∑ i, star (p i) * ((normalizedArray x)^k).mulVec q i‖}).toReal ≤ _
  simpa only [Set.preimage_setOf_eq, normalizedPowerBilinear_eq_normalizedArray] using hb

#print axioms iidNestedPowerBilinear_probability_le
end SpectralRadiusUpperTail
