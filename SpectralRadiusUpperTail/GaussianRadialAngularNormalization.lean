import SpectralRadiusUpperTail.GaussianCoordinateIntegral
import SpectralRadiusUpperTail.GaussianPolarInversePower
import SpectralRadiusUpperTail.GaussianMarkedRealSphereArea

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal

theorem gaussian_radial_lintegral_eq_setLIntegral (m : ℕ) :
    (∫⁻ r : Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-1*r.val^2))
      ∂Measure.volumeIoiPow m) =
      ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r^m) *
        ENNReal.ofReal (Real.exp (-r^2)) := by
  unfold Measure.volumeIoiPow
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simpa only [Pi.mul_apply, neg_mul, one_mul] using
    lintegral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r^m) * ENNReal.ofReal (Real.exp (-r^2)))

theorem gaussian_radial_sphere_product (m : ℕ) :
    ENNReal.ofReal ((Real.sqrt Real.pi)^(m+1)) =
      ENNReal.ofReal (2 * (Real.sqrt Real.pi)^(m+1) /
        Real.Gamma (((m : ℝ)+1)/2)) *
      ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r^m) *
        ENNReal.ofReal (Real.exp (-r^2)) := by
  let E := EuclideanSpace ℝ (Fin (m+1))
  have hid := gaussian_polar_inverse_power (volume : Measure E)
    (LinearMap.id : E →ₗ[ℝ] E) (by
      intro v
      simpa only [LinearMap.id_coe, id_eq, mem_sphere_zero_iff_norm.mp v.property]
        using (zero_lt_one : (0 : ℝ) < 1))
  have hnorm (v : sphere (0 : E) 1) : ‖(LinearMap.id : E →ₗ[ℝ] E) v.val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp v.property
  simp_rw [hnorm, one_pow, inv_one, ENNReal.ofReal_one, lintegral_one] at hid
  simp only [LinearMap.id_coe, id_eq] at hid
  change (∫⁻ x : E, ENNReal.ofReal (Real.exp (-‖x‖^2))) = _ at hid
  rw [euclideanGaussian_lintegral,
    euclidean_realSphere_surfaceArea (m+1) (by omega)] at hid
  simpa only [E, finrank_euclideanSpace, Fintype.card_fin, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one, gaussian_radial_lintegral_eq_setLIntegral] using hid

theorem gaussian_radial_setLIntegral_bounds (m : ℕ) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r^m) *
      ENNReal.ofReal (Real.exp (-r^2))) ≠ 0 ∧
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r^m) *
      ENNReal.ofReal (Real.exp (-r^2))) ≠ ∞ := by
  rw [← gaussian_radial_lintegral_eq_setLIntegral]
  exact gaussian_radial_normalizer_bounds m 1 (by norm_num)

#print axioms gaussian_radial_lintegral_eq_setLIntegral
#print axioms gaussian_radial_sphere_product
#print axioms gaussian_radial_setLIntegral_bounds
end SpectralRadiusUpperTail
