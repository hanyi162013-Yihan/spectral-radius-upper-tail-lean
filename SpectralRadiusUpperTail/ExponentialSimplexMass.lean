import SpectralRadiusUpperTail.SimplexHalfMass

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma exponential_product_simplex_half (m : ℕ) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∑ i, ENNReal.ofReal (r i)⁻¹ ≤ 1/2) :
    (1/2 : ℝ≥0∞) ≤ (Measure.pi (fun i => expMeasure (r i))) (positiveSimplex m) := by
  letI (i : Fin m) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  apply simplex_mass_ge_half
  · apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun j => expMeasure (r j)) i).quasiMeasurePreserving.ae
      (exponential_nonnegative_ae (r i) (hr i))
  · rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
    simp_rw [(measurePreserving_eval (fun j => expMeasure (r j)) _).lintegral_comp
      (show Measurable (fun x : ℝ => ENNReal.ofReal x) by fun_prop)]
    simpa only [exponential_firstMoment_lintegral _ (hr _)] using hs

lemma exponential_product_simplex_half_of_rates (m : ℕ) (r : Fin m → ℝ)
    (hr : ∀ i, 2*((m : ℝ)+1) ≤ r i) :
    (1/2 : ℝ≥0∞) ≤ (Measure.pi (fun i => expMeasure (r i))) (positiveSimplex m) := by
  have hp : ∀ i, 0 < r i := fun i => lt_of_lt_of_le (by positivity) (hr i)
  apply exponential_product_simplex_half m r hp
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => inv_nonneg.mpr (hp i).le)]
  have hsum : ∑ i : Fin m, (r i)⁻¹ ≤ (1/2 : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin m, (2*((m : ℝ)+1))⁻¹ :=
        Finset.sum_le_sum (fun i _ => inv_anti₀ (by positivity) (hr i))
      _ = (m : ℝ)/(2*((m : ℝ)+1)) := by simp [div_eq_mul_inv]
      _ ≤ 1/2 := by apply (div_le_iff₀ (by positivity)).mpr; linarith
  simpa using ENNReal.ofReal_le_ofReal hsum

#print axioms exponential_product_simplex_half
#print axioms exponential_product_simplex_half_of_rates
end SpectralRadiusUpperTail
