import SpectralRadiusUpperTail.ComplexVaryingSetSphereAverage

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal BigOperators

lemma complex_varying_set_sphere_average_scaled (n M : ℕ) (hn : 0 < n) (hMn : M ≤ n)
    (c : ℝ) (hc : 0 < c) (D : ℝ≥0∞) (hD : D ≠ 0) (hDtop : D ≠ ∞)
    (f : sphere (0 : EuclideanSpace ℂ (Fin n)) 1 → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ v, ∃ I : Finset (Fin n), I.card ≤ M ∧
      f v ≤ D*ENNReal.ofReal ((c/(c+Iᶜ.sum (fun j => ‖v.val j‖^2)))^n)) :
    (∫⁻ v, f v ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) ≤
      D*ENNReal.ofReal (((M+1 : ℕ) : ℝ)*((n : ℝ)+1)^M*(c/(c+1))^(n-M)) := by
  have hb := complex_varying_set_sphere_average n M hn hMn c hc (fun v => D⁻¹*f v) (by
    intro v
    obtain ⟨I, hI, hi⟩ := hf v
    refine ⟨I, hI, ?_⟩
    have hh := mul_le_mul' (le_refl D⁻¹) hi
    rw [ENNReal.inv_mul_cancel_left hD hDtop] at hh
    exact hh)
  rw [lintegral_const_mul _ hfm] at hb
  have hh := mul_le_mul' (le_refl D) hb
  rw [← mul_assoc, ENNReal.mul_inv_cancel hD hDtop, one_mul] at hh
  exact hh

#print axioms complex_varying_set_sphere_average_scaled
end SpectralRadiusUpperTail
