import SpectralRadiusUpperTail.ComplexFiniteAnnealedBound
import SpectralRadiusUpperTail.ComplexLightRowEstimate
import SpectralRadiusUpperTail.AnnealedPolynomialBudget
import SpectralRadiusUpperTail.ComplexUpperRateAlgebra

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The actual sharp-subgaussian full-sphere annealed estimate. -/
lemma complex_fullSphere_annealed_bound (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : ℂ => x) 2 μ)
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0) (h3 : Integrable (fun x : ℂ => ‖x‖^3) μ)
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (R a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
      (∫⁻ x : Fin n → Fin n → ℂ, fullSpectralSphereWeight n a z x
        ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤
          ENNReal.ofReal (Real.exp ((n : ℝ)*(complexAnnealedExponent a ‖z‖+ε))) := by
  let r := a/(a+1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := (div_le_one (by positivity : 0 < a+1)).mpr (by linarith)
  let D := -Real.log r
  have hD : 0 ≤ D := neg_nonneg.mpr (Real.log_nonpos hr.le hr1)
  obtain ⟨K, hK, hcost⟩ := exists_large_target_cutoff R D (ε/3) hD (by positivity)
  obtain ⟨C, hC, hlight⟩ := complex_light_row_estimate μ hX hm hv hp h3 hint hmgf a ha
  let b := r*Real.exp (-K^2/(a+1))
  have hb : 0 < b := mul_pos hr (Real.exp_pos _)
  let δ := (Real.exp (ε/3)-1)*b
  have hδ : 0 < δ := mul_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))) hb
  let d := δ/(C+1)
  have hd : 0 < d := div_pos hδ (by linarith)
  have hCd : C*d ≤ δ := by
    have he : (C+1)*d = δ := mul_div_cancel₀ _ (by linarith : C+1 ≠ 0)
    nlinarith
  obtain ⟨M, hM⟩ := largeCoordinateSet_uniform_card d hd
  have hbudget := eventually_annealed_polynomial_budget M r hr (ε/3) (by positivity)
  filter_upwards [hbudget, eventually_ge_atTop M, eventually_gt_atTop 0] with n hn hMn hn0 z hz
  have hfinite := complex_fullSphere_finite_bound_of_light μ hint hmgf n M hn0 hMn a K (ε/3) (C*d) d
    ha hK (by positivity) hCd
    (fun v hv => hM n v hv.le)
    (fun v hv t => hlight n (largeCoordinateSet d v) v hv d hd.le (largeCoordinateSet_small d v) t) z
  let B := -‖z‖^2/(a+1)+ε/3+(‖z‖^2/K^2)*D
  have hpoly := hn B
  have htotal := hfinite.trans (ENNReal.ofReal_le_ofReal hpoly)
  apply htotal.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  have hc := hcost (‖z‖^2) (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg z) hz 2)
  dsimp [B, complexAnnealedExponent]
  rw [show (1+a : ℝ) = a+1 by ring]
  change Real.log r+(-‖z‖^2/(a+1)+ε/3+(‖z‖^2/K^2)*D)+ε/3 ≤
    Real.log r-‖z‖^2/(a+1)+ε
  rw [neg_div]
  linarith only [hc]

#print axioms complex_fullSphere_annealed_bound
end SpectralRadiusUpperTail
