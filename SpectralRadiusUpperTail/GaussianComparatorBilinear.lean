import SpectralRadiusUpperTail.IidNestedBilinear
import SpectralRadiusUpperTail.GaussianSequentialMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The iid first-power bound holds for the actual comparator on the retained coupling. -/
lemma gaussianComparatorBilinear_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (p q : Fin N → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hp : ∑ i, ‖p i‖^2 ≤ 1) (hq : ∑ j, ‖q j‖^2 ≤ 1)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (t : Fin N → 𝕂)
    (ε : ℝ) (hε : 0 < ε) :
    (gaussianSequentialMatrixLaw μ v a t).real
      {x | ε ≤ ‖∑ i, star (p i)*
        ((normalizedArray (fun k => comparatorVector N (x k))).mulVec q) i‖} ≤
      (1/(N : ℝ))/ε^2 := by
  have hb := iidNestedBilinear_probability_le μ p q hX hm hv hp hq ε hε
  have hs : MeasurableSet {x : Fin N → Fin N → 𝕂 |
      ε ≤ ‖∑ i, star (p i)*((normalizedArray x).mulVec q) i‖} :=
    measurableSet_le measurable_const (by unfold normalizedArray Matrix.mulVec dotProduct; fun_prop)
  have hf : Measurable (fun (x : Fin N → Fin N → 𝕂 × 𝕂) i => comparatorVector N (x i)) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_comparatorVector (α := 𝕂) N).comp (measurable_pi_apply i))
  rw [← gaussianSequentialMatrixLaw_comparator μ v a ha t] at hb
  change (((gaussianSequentialMatrixLaw μ v a t).map
    (fun x i => comparatorVector N (x i)))
      {x | ε ≤ ‖∑ i, star (p i)*((normalizedArray x).mulVec q) i‖}).toReal ≤ _ at hb
  rw [Measure.map_apply hf hs] at hb
  exact hb

#print axioms gaussianComparatorBilinear_probability_le
end SpectralRadiusUpperTail
