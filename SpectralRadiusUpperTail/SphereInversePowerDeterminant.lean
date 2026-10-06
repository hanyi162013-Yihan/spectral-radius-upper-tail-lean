import SpectralRadiusUpperTail.GaussianPolarInversePower

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma sphere_inverse_power_determinant (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E →ₗ[ℝ] E) (hA : LinearMap.det A ≠ 0)
    (hpos : ∀ v : sphere (0 : E) 1, 0 < ‖A v.val‖) :
    (∫⁻ v : sphere (0 : E) 1, ENNReal.ofReal ((‖A v.val‖^(Module.finrank ℝ E))⁻¹)
      ∂haarSphereProbability μ) = ENNReal.ofReal |(LinearMap.det A)⁻¹| := by
  let J := ∫⁻ r : Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-1*r.val^2))
    ∂Measure.volumeIoiPow (Module.finrank ℝ E-1)
  have hJ := gaussian_radial_normalizer_bounds (Module.finrank ℝ E-1) 1 (by norm_num)
  have hpol := gaussian_polar_inverse_power μ A hpos
  have hid := gaussian_polar_inverse_power μ (LinearMap.id : E →ₗ[ℝ] E) (by
    intro v
    simpa only [LinearMap.id_coe, id_eq, mem_sphere_zero_iff_norm.mp v.property] using (zero_lt_one : (0 : ℝ) < 1))
  have hnorm (v : sphere (0 : E) 1) : ‖(LinearMap.id : E →ₗ[ℝ] E) v.val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp v.property
  simp_rw [hnorm, one_pow, inv_one, ENNReal.ofReal_one, lintegral_one] at hid
  simp only [LinearMap.id_coe, id_eq] at hid
  have hg := gaussian_linear_lintegral μ A hA 1
  simp only [neg_mul, one_mul] at hg
  have he : (∫⁻ v : sphere (0 : E) 1, ENNReal.ofReal ((‖A v.val‖^(Module.finrank ℝ E))⁻¹)
        ∂μ.toSphere)*J = (ENNReal.ofReal |(LinearMap.det A)⁻¹| * μ.toSphere Set.univ)*J := by
    rw [← hpol, hg, hid]
    exact mul_assoc _ _ _ |>.symm
  have hraw := (ENNReal.mul_left_inj hJ.1 hJ.2).mp he
  rw [haarSphereProbability_lintegral, hraw]
  have hS0 : μ.toSphere Set.univ ≠ 0 := by
    intro h
    exact Measure.toSphere_ne_zero μ (Measure.measure_univ_eq_zero.mp h)
  rw [mul_left_comm, ENNReal.inv_mul_cancel hS0 (measure_ne_top _ _), mul_one]

#print axioms sphere_inverse_power_determinant
end SpectralRadiusUpperTail
