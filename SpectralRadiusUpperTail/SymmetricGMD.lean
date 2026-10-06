import SpectralRadiusUpperTail.DominatedMatrixTail
import SpectralRadiusUpperTail.GaussianExactMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Nat

theorem symmetric_odd_moment_zero (μ : Measure ℝ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (m : ℕ) :
    (∫ x : ℝ, x^(2*m+1) ∂μ) = 0 := by
  have h : (∫ x : ℝ, x^(2*m+1) ∂μ) = -(∫ x : ℝ, x^(2*m+1) ∂μ) := by
    calc
      (∫ x : ℝ, x^(2*m+1) ∂μ) = ∫ x : ℝ, x^(2*m+1) ∂μ.map (fun x => -x) := by
        rw [hsym]
      _ = ∫ x : ℝ, (-x)^(2*m+1) ∂μ := integral_map (by fun_prop) (by fun_prop)
      _ = -(∫ x : ℝ, x^(2*m+1) ∂μ) := by
        simp [pow_add, pow_mul, integral_neg]
  linarith

theorem symmetric_moment_nonneg (μ : Measure ℝ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (k : ℕ) :
    0 ≤ ∫ x : ℝ, x^k ∂μ := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · rw [hm]
    exact integral_nonneg (fun x => by rw [pow_mul]; positivity)
  · rw [hm, symmetric_odd_moment_zero μ hsym]

theorem symmetric_gmd_moment_le_standardNormal (μ : Measure ℝ)
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (heven : ∀ m, (∫ x : ℝ, x^(2*m) ∂μ) ≤ ((2*m-1)‼ : ℝ)) (k : ℕ) :
    (∫ x : ℝ, x^k ∂μ) ≤ ∫ x : ℝ, x^k ∂standardNormal := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · rw [hm, standardNormal_even_moment]
    exact heven m
  · rw [hm, symmetric_odd_moment_zero μ hsym, standardNormal_odd_moment]

/-- The manuscript's symmetric Gaussian-even-moment hypothesis gives an actual finite
matrix-tail bound. Integrability is explicit because Lean's Bochner integral alone is
zero on nonintegrable functions and must not be used to encode finite moments. -/
theorem symmetric_gmd_matrix_spectral_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : ∀ k, Integrable (fun x : ℝ => x^k) μ)
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (heven : ∀ m, (∫ x : ℝ, x^(2*m) ∂μ) ≤ ((2*m-1)‼ : ℝ))
    (n k : ℕ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) :
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
        {x | r ≤ realMatrixRadius ((1 / Real.sqrt n) • entryMatrix x)} ≤
      (∫ x, scaledFrobeniusPowerSquared (1 / Real.sqrt n) k x ∂gaussianMatrixLaw n) /
        r^(2*k) :=
  dominated_matrix_spectral_tail_le_moment (fun _ => μ) (fun _ => standardNormal)
    (fun _ => hint) (fun _ => standardNormal_pow_integrable)
    (fun _ => symmetric_moment_nonneg μ hsym)
    (fun _ => symmetric_gmd_moment_le_standardNormal μ hsym heven)
    (1 / Real.sqrt n) r hr k hk

#print axioms symmetric_gmd_matrix_spectral_tail
end SpectralRadiusUpperTail
