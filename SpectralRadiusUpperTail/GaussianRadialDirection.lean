import SpectralRadiusUpperTail.HaarSphereDirection
import SpectralRadiusUpperTail.PositiveWeightNormalizer
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal

lemma volumeIoiPow_ne_zero (k : ℕ) : Measure.volumeIoiPow k ≠ 0 := by
  have hp : 0 < Measure.volumeIoiPow k (Set.Iio (⟨1,by norm_num⟩ : Set.Ioi (0 : ℝ))) := by
    rw [Measure.volumeIoiPow_apply_Iio]
    apply ENNReal.ofReal_pos.mpr
    positivity
  intro h
  rw [h] at hp
  simpa using hp

lemma gaussian_radial_integrable (k : ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun r : Set.Ioi (0 : ℝ) => Real.exp (-c*r.val^2)) (Measure.volumeIoiPow k) := by
  have hi : IntegrableOn (fun r : ℝ => r^k*Real.exp (-c*r^2)) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast] using
      integrableOn_rpow_mul_exp_neg_mul_sq hc (by have h := Nat.cast_nonneg (α := ℝ) k; linarith : (-1 : ℝ) < (k : ℝ))
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).1 hi
  unfold Measure.volumeIoiPow
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  convert hs using 1
  funext r
  simp only [Function.comp_apply,ENNReal.toReal_ofReal (pow_nonneg r.property.le k),smul_eq_mul]

lemma gaussian_radial_normalizer_bounds (k : ℕ) (c : ℝ) (hc : 0 < c) :
    (∫⁻ r : Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-c*r.val^2)) ∂Measure.volumeIoiPow k) ≠ 0 ∧
    (∫⁻ r : Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-c*r.val^2)) ∂Measure.volumeIoiPow k) ≠ ∞ := by
  letI : NeZero (Measure.volumeIoiPow k) := ⟨volumeIoiPow_ne_zero k⟩
  exact positiveWeight_lintegral_bounds _ _ (gaussian_radial_integrable k c hc)
    (fun _ => Real.exp_pos _)

lemma gaussian_radial_direction_eq_haarSphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (c : ℝ) (hc : 0 < c) :
    (normalizedTilt (μ.comap (Subtype.val : ({0}ᶜ : Set E) → E))
      (fun x => ENNReal.ofReal (Real.exp (-c*‖x.val‖^2)))).map
        (fun x => (homeomorphUnitSphereProd E x).1) = haarSphereProbability μ := by
  have hz := gaussian_radial_normalizer_bounds (Module.finrank ℝ E-1) c hc
  have hh := radial_density_direction_eq_haarSphere μ
    (fun r : Set.Ioi (0 : ℝ) => ENNReal.ofReal (Real.exp (-c*r.val^2))) (by fun_prop) hz.1 hz.2
  simpa only [homeomorphUnitSphereProd_apply_snd_coe] using hh

#print axioms volumeIoiPow_ne_zero
#print axioms gaussian_radial_integrable
#print axioms gaussian_radial_normalizer_bounds
#print axioms gaussian_radial_direction_eq_haarSphere
end SpectralRadiusUpperTail
