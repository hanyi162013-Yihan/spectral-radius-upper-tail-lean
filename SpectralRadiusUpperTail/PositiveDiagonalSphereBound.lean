import SpectralRadiusUpperTail.PositiveExponentialCoordinate
import SpectralRadiusUpperTail.ComplexDiagonalSphereIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma positive_exponential_normalized_lower (m : ℕ) (i : Fin (m+1)) (a : ℝ)
    (ha : 0 ≤ a) (h : Fin (m+1) → ℝ) (hh : ∀ j, 0 ≤ h j) :
    (1/2 : ℝ≥0∞)*ENNReal.ofReal (Real.exp (a*h i/2-2*((m : ℝ)+1))) ≤
      ∫⁻ y : Fin (m+1) → ℝ,
        ENNReal.ofReal (Real.exp (a*((∑ j, h j*y j)/(∑ j, y j))))
        ∂Measure.pi (fun _ => expMeasure (1/2)) := by
  have he := exponential_normalized_integral_split m i (-a) 1 h
  simp only [div_one, neg_neg] at he
  rw [he]
  let N : ℝ := (m : ℝ)+1
  let P := Measure.pi (fun _ : Fin m => expMeasure (1/2))
  let C := ENNReal.ofReal (Real.exp (a*h i/2))*ENNReal.ofReal (Real.exp (-2*N))
  have hb : (∫⁻ _y in positiveSimplexAt m (4*N), C ∂P) ≤
      ∫⁻ y in positiveSimplexAt m (4*N), ∫⁻ y₀ : ℝ,
        exponentialWitnessIntegrand (-a) 1 (h i) (fun j => h (i.succAbove j)) y₀ y
        ∂expMeasure (1/2) ∂P := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (positiveSimplexAt_measurable m (4*N))] with y hy
    exact positive_exponential_first_coordinate N a (h i) (fun j => h (i.succAbove j)) y
      (by dsimp [N]; positivity) ha (hh i) (fun j => hh _) hy.1 hy.2
  rw [lintegral_const, Measure.restrict_apply_univ] at hb
  have hm := exponential_half_rate_simplex m N (by dsimp [N]; positivity) (by dsimp [N]; linarith)
  have hl := (mul_le_mul' (le_refl C) hm).trans hb
  have hall := hl.trans (setLIntegral_le_lintegral _ _)
  have hc : C = ENNReal.ofReal (Real.exp (a*h i/2-2*((m : ℝ)+1))) := by
    dsimp [C, N]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  rw [hc, mul_comm] at hall
  exact hall

lemma complex_positive_diagonal_sphere_lower (n : ℕ) (hn : 0 < n) (i : Fin n)
    (a : ℝ) (ha : 0 ≤ a) (h : Fin n → ℝ) (hh : ∀ j, 0 ≤ h j) :
    (1/2 : ℝ≥0∞)*ENNReal.ofReal (Real.exp (a*h i/2-2*(n : ℝ))) ≤
      complexDiagonalSphereIntegral n (-a) h := by
  rw [complexDiagonalSphereIntegral_exponential n hn]
  simp only [neg_neg]
  cases n with
  | zero => omega
  | succ m =>
      simpa only [Nat.cast_add, Nat.cast_one] using positive_exponential_normalized_lower m i a ha h hh

#print axioms positive_exponential_normalized_lower
#print axioms complex_positive_diagonal_sphere_lower
end SpectralRadiusUpperTail
