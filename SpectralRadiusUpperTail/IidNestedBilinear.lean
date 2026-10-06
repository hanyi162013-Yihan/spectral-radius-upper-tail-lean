import SpectralRadiusUpperTail.IidBilinearProbability
import SpectralRadiusUpperTail.IidBilinearMatrix
import SpectralRadiusUpperTail.IidMatrixFlatten

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {N : ℕ}

/-- The same actual first-power tail bound on the nested iid comparator law. -/
lemma iidNestedBilinear_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (p q : Fin N → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hp : ∑ i, ‖p i‖^2 ≤ 1) (hq : ∑ j, ‖q j‖^2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin N => μ))).real
      {x | ε ≤ ‖∑ i, star (p i)*((normalizedArray x).mulVec q) i‖} ≤
      (1/(N : ℝ))/ε^2 := by
  have hb := iidBilinear_probability_le μ p q hX hm hv hp hq ε hε
  have hs : MeasurableSet {x | ε ≤ ‖iidBilinear p q x‖} :=
    measurableSet_le measurable_const (by unfold iidBilinear; fun_prop)
  rw [← iid_matrix_flatten_law μ N] at hb
  change (((Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin N => μ))).map
    (fun x : Fin N → Fin N → 𝕂 => fun ij : Fin N × Fin N => x ij.1 ij.2))
      {x | ε ≤ ‖iidBilinear p q x‖}).toReal ≤ _ at hb
  rw [Measure.map_apply (by fun_prop) hs] at hb
  change ((Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin N => μ)))
    {x | ε ≤ ‖∑ i, star (p i)*((normalizedArray x).mulVec q) i‖}).toReal ≤ _
  simpa only [Set.preimage_setOf_eq, iidBilinear_eq_normalized_matrix] using hb

#print axioms iidNestedBilinear_probability_le
end SpectralRadiusUpperTail
