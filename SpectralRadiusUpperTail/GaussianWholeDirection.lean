import SpectralRadiusUpperTail.GaussianRadialDirection
import SpectralRadiusUpperTail.GaussianNormIntegrable

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma gaussian_whole_direction_eq_haarSphere (μ : Measure E) [μ.IsAddHaarMeasure]
    (c : ℝ) (hc : 0 < c) :
    (normalizedTilt μ (fun x => ENNReal.ofReal (Real.exp (-c*‖x‖^2)))).map
      (fun x => ‖x‖⁻¹ • x) = (haarSphereProbability μ).map Subtype.val := by
  have hp : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
      (μ.comap Subtype.val) μ := by
    have hh := measurePreserving_subtype_coe (μa := μ) (measurableSet_singleton (0 : E)).compl
    simpa only [restrict_compl_singleton] using hh
  have hd : Measurable (fun x : E => ‖x‖⁻¹ • x) := by fun_prop
  have he := normalizedTilt_map_measurePreserving _ _ (Subtype.val : ({0}ᶜ : Set E) → E) hp
    (fun x => ENNReal.ofReal (Real.exp (-c*‖x‖^2))) (by fun_prop)
    (gaussian_norm_normalizer_bounds μ c hc).1
  rw [← he,Measure.map_map hd measurable_subtype_coe]
  have hs := congrArg (fun ρ : Measure (sphere (0 : E) 1) => ρ.map Subtype.val)
    (gaussian_radial_direction_eq_haarSphere μ c hc)
  have hm : Measurable (fun x : ({0}ᶜ : Set E) => (homeomorphUnitSphereProd E x).1) :=
    (continuous_fst.comp (homeomorphUnitSphereProd E).continuous).measurable
  rw [Measure.map_map measurable_subtype_coe hm] at hs
  simpa only [Function.comp_def,homeomorphUnitSphereProd_apply_fst_coe] using hs

#print axioms gaussian_whole_direction_eq_haarSphere
end SpectralRadiusUpperTail
