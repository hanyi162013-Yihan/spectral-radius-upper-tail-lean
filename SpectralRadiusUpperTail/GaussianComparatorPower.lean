import SpectralRadiusUpperTail.IidNestedPowerBilinear
import SpectralRadiusUpperTail.GaussianSequentialMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n k : ℕ}

lemma gaussianComparatorPower_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (t : Fin n → 𝕂)
    (ε : ℝ) (hε : 0 < ε) :
    (gaussianSequentialMatrixLaw μ v a t).real
      {x | ε ≤ ‖∑ i, star (p i) *
        ((normalizedArray (fun j => comparatorVector n (x j)))^k).mulVec q i‖} ≤
      (pairedMomentConstant μ k/(n : ℝ))/ε^2 := by
  have hb := iidNestedPowerBilinear_probability_le μ c hc hexp hm hk hn p q hp hq ε hε
  have hs : MeasurableSet {x : Fin n → Fin n → 𝕂 |
      ε ≤ ‖∑ i, star (p i) * ((normalizedArray x)^k).mulVec q i‖} :=
    measurableSet_le measurable_const (measurable_normalizedArray_power_bilinear p q k).norm
  have hf : Measurable (fun (x : Fin n → Fin n → 𝕂 × 𝕂) i => comparatorVector n (x i)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_comparatorVector (α := 𝕂) n).comp (measurable_pi_apply i))
  rw [← gaussianSequentialMatrixLaw_comparator μ v a ha t] at hb
  change (((gaussianSequentialMatrixLaw μ v a t).map
    (fun x i => comparatorVector n (x i)))
      {x | ε ≤ ‖∑ i, star (p i) * ((normalizedArray x)^k).mulVec q i‖}).toReal ≤ _ at hb
  rw [Measure.map_apply hf hs] at hb
  exact hb

#print axioms gaussianComparatorPower_probability_le
end SpectralRadiusUpperTail
