import SpectralRadiusUpperTail.HaarBallComparison

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma haarSphereProbability_lintegral (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : sphere (0 : E) 1 → ℝ≥0∞) :
    (∫⁻ v, f v ∂haarSphereProbability μ) = (μ.toSphere Set.univ)⁻¹ * ∫⁻ v, f v ∂μ.toSphere := by
  simp [haarSphereProbability,normalizedTilt,withDensity_const,lintegral_smul_measure,smul_eq_mul]

lemma sphere_integral_mul_ball_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (hf : Measurable f)
    (hmono : ∀ v : sphere (0 : E) 1, ∀ r : ℝ, 0 < r → r < 1 → f v.val ≤ f (r • v.val)) :
    (∫⁻ v : sphere (0 : E) 1, f v.val ∂haarSphereProbability μ) * μ (ball 0 1) ≤
      ∫⁻ x, f x ∂μ := by
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hV0 : μ (ball (0 : E) 1) ≠ 0 := isOpen_ball.measure_ne_zero μ (nonempty_ball.mpr zero_lt_one)
  have hVtop : μ (ball (0 : E) 1) ≠ ∞ := ne_of_lt measure_ball_lt_top
  have hh := sphere_radial_integral_lower μ f hf hmono
  rw [Measure.volumeIoiPow_apply_Iio] at hh
  have hdr : ((Module.finrank ℝ E-1 : ℕ) : ℝ)+1 = (Module.finrank ℝ E : ℝ) := by
    rw [Nat.cast_sub hd,Nat.cast_one]
    ring
  simp only [one_pow,hdr] at hh
  have hc : ENNReal.ofReal (1/((Module.finrank ℝ E : ℕ) : ℝ)) =
      (Module.finrank ℝ E : ℝ≥0∞)⁻¹ := by
    rw [one_div,ENNReal.ofReal_inv_of_pos (by exact_mod_cast hd),ENNReal.ofReal_natCast]
  rw [hc] at hh
  rw [haarSphereProbability_lintegral,Measure.toSphere_apply_univ]
  have he : (((Module.finrank ℝ E : ℝ≥0∞)*μ (ball (0 : E) 1))⁻¹ *
      ∫⁻ v : sphere (0 : E) 1, f v.val ∂μ.toSphere) * μ (ball 0 1) =
      (∫⁻ v : sphere (0 : E) 1, f v.val ∂μ.toSphere) * (Module.finrank ℝ E : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inr hVtop) (Or.inr hV0)]
    calc
      _ = (∫⁻ v : sphere (0 : E) 1, f v.val ∂μ.toSphere) * (Module.finrank ℝ E : ℝ≥0∞)⁻¹ *
          ((μ (ball (0 : E) 1))⁻¹ * μ (ball 0 1)) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hV0 hVtop,mul_one]
  rw [he]
  exact hh

#print axioms haarSphereProbability_lintegral
#print axioms sphere_integral_mul_ball_le
end SpectralRadiusUpperTail
