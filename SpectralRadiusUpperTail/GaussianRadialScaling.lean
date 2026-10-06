import SpectralRadiusUpperTail.GaussianRadialDirection
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal

lemma gaussian_radial_integral_eq_setIntegral (k : ℕ) (c : ℝ) :
    (∫ r : Ioi (0 : ℝ), Real.exp (-c*r.val^2) ∂Measure.volumeIoiPow k) =
      ∫ r in Ioi (0 : ℝ), r^k*Real.exp (-c*r^2) := by
  unfold Measure.volumeIoiPow
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  calc
    _ = ∫ r : Ioi (0 : ℝ), r.val^k*Real.exp (-c*r.val^2)
        ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        dsimp only
        rw [ENNReal.toReal_ofReal (pow_nonneg r.property.le k)])
    _ = _ := integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r^k*Real.exp (-c*r^2))

lemma gaussian_radial_integral_scale (k : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫ r : Ioi (0 : ℝ), Real.exp (-s^2*r.val^2) ∂Measure.volumeIoiPow k) =
      (s^(k+1))⁻¹*(∫ r : Ioi (0 : ℝ), Real.exp (-1*r.val^2) ∂Measure.volumeIoiPow k) := by
  rw [gaussian_radial_integral_eq_setIntegral, gaussian_radial_integral_eq_setIntegral]
  have hh := integral_comp_mul_left_Ioi (fun r : ℝ => r^k*Real.exp (-r^2)) 0 hs
  simp only [mul_zero, smul_eq_mul, mul_pow] at hh
  have he (r : ℝ) : s^k*r^k*Real.exp (-(s^2*r^2)) =
      s^k*(r^k*Real.exp (-s^2*r^2)) := by rw [neg_mul]; ring
  simp_rw [he] at hh
  rw [integral_const_mul] at hh
  apply mul_left_cancel₀ (pow_ne_zero k hs.ne')
  rw [hh, ← mul_assoc]
  have hc : s^k*(s^(k+1))⁻¹ = s⁻¹ := by rw [pow_succ]; field_simp
  rw [hc]
  simp only [neg_mul, one_mul]

lemma gaussian_radial_lintegral_scale (k : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s^2*r.val^2)) ∂Measure.volumeIoiPow k) =
      ENNReal.ofReal ((s^(k+1))⁻¹)*
        ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-1*r.val^2)) ∂Measure.volumeIoiPow k := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_radial_integrable k (s^2) (sq_pos_of_pos hs))
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (gaussian_radial_integrable k 1 (by norm_num))
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)), gaussian_radial_integral_scale k s hs,
    ENNReal.ofReal_mul (by positivity)]

#print axioms gaussian_radial_integral_eq_setIntegral
#print axioms gaussian_radial_integral_scale
#print axioms gaussian_radial_lintegral_scale
end SpectralRadiusUpperTail
