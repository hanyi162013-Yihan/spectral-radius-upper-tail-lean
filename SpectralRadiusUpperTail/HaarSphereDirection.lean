import SpectralRadiusUpperTail.RadialProductDirection
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def haarSphereProbability (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  normalizedTilt μ.toSphere (fun _ => 1)

lemma haarSphereProbability_probability (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsProbabilityMeasure (haarSphereProbability μ) := by
  letI : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  apply normalizedTilt_probability
  · simpa using (NeZero.ne (μ.toSphere Set.univ))
  · simpa using (measure_ne_top μ.toSphere Set.univ)

lemma radial_density_direction_eq_haarSphere (μ : Measure E) [μ.IsAddHaarMeasure]
    (g : Set.Ioi (0 : ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : (∫⁻ r, g r ∂Measure.volumeIoiPow (Module.finrank ℝ E-1)) ≠ 0)
    (hgtop : (∫⁻ r, g r ∂Measure.volumeIoiPow (Module.finrank ℝ E-1)) ≠ ∞) :
    (normalizedTilt (μ.comap (Subtype.val : ({0}ᶜ : Set E) → E))
      (fun x => g (homeomorphUnitSphereProd E x).2)).map
        (fun x => (homeomorphUnitSphereProd E x).1) = haarSphereProbability μ := by
  letI : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  have hp := μ.measurePreserving_homeomorphUnitSphereProd
  have hw : Measurable (fun p : sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => g p.2) :=
    hg.comp measurable_snd
  have hZ : (∫⁻ p : sphere (0 : E) 1 × Set.Ioi (0 : ℝ), g p.2
      ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1))) ≠ 0 := by
    rw [lintegral_prod _ hw.aemeasurable]
    simpa only [lintegral_const] using mul_ne_zero hg0 (NeZero.ne (μ.toSphere Set.univ))
  have he := normalizedTilt_map_measurePreserving _ _ (homeomorphUnitSphereProd E) hp
    (fun p => g p.2) hw hZ
  have hm := congrArg (fun ρ => Measure.map Prod.fst ρ) he
  rw [Measure.map_map measurable_fst hp.measurable,
    normalizedTilt_prod_radial_direction μ.toSphere _ g hg hg0 hgtop] at hm
  exact hm

#print axioms haarSphereProbability
#print axioms haarSphereProbability_probability
#print axioms radial_density_direction_eq_haarSphere
end SpectralRadiusUpperTail
