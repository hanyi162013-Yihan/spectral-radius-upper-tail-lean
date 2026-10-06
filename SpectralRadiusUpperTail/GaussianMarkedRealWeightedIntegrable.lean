import SpectralRadiusUpperTail.GaussianMarkedRealDensityIntegrable

namespace SpectralRadiusUpperTail
open MeasureTheory Set

theorem gaussianMarkedRealDensity_weighted_bounds
    (n k : ℕ) (hn : 0 < n) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ x^(2*k)*gaussianMarkedRealDensity n x ∧
    x^(2*k)*gaussianMarkedRealDensity n x ≤
      (n : ℝ)*(x^(2*k)*realGinibreCoreDensity n x) := by
  have hxpos : 0 < x := by linarith
  have hcore := (realGinibreCoreDensity_pos n hn x hxpos).le
  obtain ⟨hl,hu⟩ := gaussianMarkedRealDensity_sandwich n hn x hx
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : gaussianMarkedRealDensity n x ≤ (n : ℝ)*realGinibreCoreDensity n x :=
    hu.trans (mul_le_mul_of_nonneg_right (by linarith) hcore)
  constructor
  · exact mul_nonneg (pow_nonneg hxpos.le _) (hcore.trans hl)
  · calc
      _ ≤ x^(2*k)*((n : ℝ)*realGinibreCoreDensity n x) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hxpos.le _)
      _ = _ := by ring

theorem gaussianMarkedRealDensity_weighted_integrableOn
    (n k : ℕ) (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => x^(2*k)*gaussianMarkedRealDensity n x) (Ioi 1) := by
  have hcore : IntegrableOn (fun x : ℝ => x^(2*k)*realGinibreCoreDensity n x) (Ioi 1) :=
    (realGinibreCoreDensity_weighted_integrableOn n k hn).mono_set
      (Ioi_subset_Ioi (by norm_num))
  apply (hcore.const_mul (n : ℝ)).mono'
    ((measurable_id.pow_const _).mul (measurable_gaussianMarkedRealDensity n)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hb := gaussianMarkedRealDensity_weighted_bounds n k hn x hx.le
  simpa only [Pi.mul_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem gaussianMarkedRealDensity_weighted_integral_le_core
    (n k : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in Ioi 1, x^(2*k)*gaussianMarkedRealDensity n x) ≤
      (n : ℝ)*(∫ x : ℝ in Ioi 1, x^(2*k)*realGinibreCoreDensity n x) := by
  have hcore : IntegrableOn (fun x : ℝ => x^(2*k)*realGinibreCoreDensity n x) (Ioi 1) :=
    (realGinibreCoreDensity_weighted_integrableOn n k hn).mono_set
      (Ioi_subset_Ioi (by norm_num))
  rw [← integral_const_mul]
  apply integral_mono_ae (gaussianMarkedRealDensity_weighted_integrableOn n k hn)
    (hcore.const_mul (n : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (gaussianMarkedRealDensity_weighted_bounds n k hn x hx.le).2

#print axioms gaussianMarkedRealDensity_weighted_bounds
#print axioms gaussianMarkedRealDensity_weighted_integrableOn
#print axioms gaussianMarkedRealDensity_weighted_integral_le_core
end SpectralRadiusUpperTail
