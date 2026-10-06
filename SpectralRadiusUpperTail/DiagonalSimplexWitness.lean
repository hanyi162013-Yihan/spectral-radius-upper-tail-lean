import SpectralRadiusUpperTail.SimplexExponentialIntegral
import SpectralRadiusUpperTail.WitnessProductAlgebra

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- The diagonal simplex integral occurring after isolating one squared coordinate. -/
noncomputable def diagonalSimplexIntegral (m : ℕ) (c h₀ : ℝ) (h : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (m.factorial : ℝ) * ENNReal.ofReal (Real.exp (-c*h₀)) *
    ∫⁻ x in positiveSimplex m, ENNReal.ofReal (Real.exp (-c*∑ i, (h i-h₀)*x i))

lemma diagonal_simplex_witness (m : ℕ) (u h₀ : ℝ) (h : Fin m → ℝ)
    (hu : 0 < u) (hh₀ : 0 ≤ h₀) (hh : ∀ i, 0 ≤ h i) :
    ENNReal.ofReal ((m.factorial : ℝ)*Real.exp (-((m+1 : ℕ) : ℝ)*h₀/u)*
      u^(m+1)/(((m+1 : ℕ) : ℝ)^m*((h₀+2*u)*∏ i, (h i+2*u)))) ≤
      diagonalSimplexIntegral m (((m+1 : ℕ) : ℝ)/u) h₀ h := by
  let r : Fin m → ℝ := fun i => ((m+1 : ℕ) : ℝ)*(h i+2*u)/u
  have hr (i : Fin m) : 2*((m : ℝ)+1) ≤ r i := by
    dsimp [r]
    apply (le_div_iff₀ hu).mpr
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ)+1 by positivity) (hh i)]
  have hcomp : (∫⁻ x in positiveSimplex m, ENNReal.ofReal (Real.exp (-(∑ i, r i*x i)))) ≤
      ∫⁻ x in positiveSimplex m,
        ENNReal.ofReal (Real.exp (-(((m+1 : ℕ) : ℝ)/u)*∑ i, (h i-h₀)*x i)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (positiveSimplex_measurable m)] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hs : (((m+1 : ℕ) : ℝ)/u)*∑ i, (h i-h₀)*x i ≤ ∑ i, r i*x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      dsimp [r]
      have ha : h i-h₀ ≤ h i+2*u := by linarith
      have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha (hx.1 i))
        (show 0 ≤ ((m+1 : ℕ) : ℝ)/u by positivity)
      convert hm using 1 <;> ring
    linarith
  have hbase := (simplex_exponential_lintegral_lower m r hr).trans hcomp
  have hp := ENNReal.ofReal_le_ofReal (witness_product_prefactor m u h₀ h hu hh₀ hh)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)] at hp
  have ht := mul_le_mul' (le_refl
    (ENNReal.ofReal (m.factorial : ℝ)*ENNReal.ofReal (Real.exp (-(((m+1 : ℕ) : ℝ)/u)*h₀))))
    (hp.trans (by simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hbase))
  unfold diagonalSimplexIntegral
  convert! ht using 1
  · rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have he : -((m+1 : ℕ) : ℝ)*h₀/u = -(((m+1 : ℕ) : ℝ)/u)*h₀ := by ring
    rw [he]
    ring

#print axioms diagonalSimplexIntegral
#print axioms diagonal_simplex_witness
end SpectralRadiusUpperTail
