import SpectralRadiusUpperTail.ArrayTruncationEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂]

lemma entryCutoff_norm_le (R : ℝ) (hR : 0 ≤ R) (z : 𝕂) : ‖entryCutoff R z‖ ≤ R := by
  by_cases h : ‖z‖ ≤ R <;> simp [entryCutoff,h,hR]

lemma entryCutoff_law_supported (μ : Measure 𝕂) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ z ∂μ.map (entryCutoff R), ‖z‖ ≤ R := by
  apply (ae_map_iff (entryCutoff_measurable R).aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  exact Filter.Eventually.of_forall (entryCutoff_norm_le R hR)

lemma entryCutoff_product_law (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ) (R : ℝ) :
    (Measure.pi (fun _ : Fin N => μ)).map (fun x : Fin N → 𝕂 => fun i => entryCutoff R (x i)) =
      Measure.pi (fun _ : Fin N => μ.map (entryCutoff R)) := by
  exact Measure.pi_map_pi (fun _ => (entryCutoff_measurable R).aemeasurable)

#print axioms entryCutoff_norm_le
#print axioms entryCutoff_law_supported
#print axioms entryCutoff_product_law
end SpectralRadiusUpperTail
