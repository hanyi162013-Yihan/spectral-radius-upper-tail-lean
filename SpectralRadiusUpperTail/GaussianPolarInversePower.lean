import SpectralRadiusUpperTail.GaussianRadialScaling
import SpectralRadiusUpperTail.GaussianLinearIntegral
import SpectralRadiusUpperTail.HaarSphereIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma gaussian_polar_inverse_power (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E →ₗ[ℝ] E) (hpos : ∀ v : sphere (0 : E) 1, 0 < ‖A v.val‖) :
    (∫⁻ x : E, ENNReal.ofReal (Real.exp (-‖A x‖^2)) ∂μ) =
      (∫⁻ v : sphere (0 : E) 1, ENNReal.ofReal ((‖A v.val‖^(Module.finrank ℝ E))⁻¹)
        ∂μ.toSphere) *
      ∫⁻ r : Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-1*r.val^2))
        ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) := by
  have hf : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-‖A x‖^2))) :=
    (Real.continuous_exp.comp (A.continuous_of_finiteDimensional.norm.pow 2).neg).measurable.ennreal_ofReal
  rw [haar_polar_lintegral μ _ hf, lintegral_prod _ (by fun_prop)]
  have he (v : sphere (0 : E) 1) :
      (∫⁻ r : Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-‖A (r.val • v.val)‖^2))
        ∂Measure.volumeIoiPow (Module.finrank ℝ E-1)) =
      ENNReal.ofReal ((‖A v.val‖^(Module.finrank ℝ E))⁻¹) *
        ∫⁻ r : Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-1*r.val^2))
          ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) := by
    have hd : Module.finrank ℝ E-1+1 = Module.finrank ℝ E := Nat.sub_add_cancel Module.finrank_pos
    have hh := gaussian_radial_lintegral_scale (Module.finrank ℝ E-1) ‖A v.val‖ (hpos v)
    rw [hd] at hh
    convert! hh using 1
    apply lintegral_congr
    intro r
    congr 2
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos r.property, mul_pow]
    ring
  simp_rw [he]
  rw [lintegral_mul_const _ (by fun_prop)]

#print axioms gaussian_polar_inverse_power
end SpectralRadiusUpperTail
