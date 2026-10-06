import SpectralRadiusUpperTail.GaussianMarkedRealWeightedIntegrable
import SpectralRadiusUpperTail.RealGinibreWeightedCoreBudget
import SpectralRadiusUpperTail.PolynomialExponentialBudget

namespace SpectralRadiusUpperTail
open MeasureTheory Set Filter
open scoped Topology

theorem gaussianMarkedRealDensity_weighted_integral_le_full_core
    (n k : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in Ioi 1, x^(2*k)*gaussianMarkedRealDensity n x) ≤
      (n : ℝ)*(∫ x : ℝ in Ioi 0, x^(2*k)*realGinibreCoreDensity n x) := by
  have hcore := realGinibreCoreDensity_weighted_integrableOn n k hn
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => x^(2*k)*realGinibreCoreDensity n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _) (realGinibreCoreDensity_pos n hn x hx).le
  have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi (by norm_num)
  exact (gaussianMarkedRealDensity_weighted_integral_le_core n k hn).trans
    (mul_le_mul_of_nonneg_left (setIntegral_mono_set hcore hnonneg hsubset.eventuallyLE)
      (Nat.cast_nonneg n))

/-- The polynomial loss in the determinant absolute-moment bound has
zero exponential cost even when the scalar weight has linear degree. -/
theorem gaussianMarkedRealDensity_weighted_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x : ℝ in Ioi 1, x^(2*k n)*gaussianMarkedRealDensity n x) ≤
        Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  have hε : 0 < δ/2 := by linarith
  have hpoly := eventually_positive_polynomial_le_exp 1 (by norm_num) 1 (δ/2) hε
  simp only [pow_one, one_mul] at hpoly
  filter_upwards [eventually_gt_atTop 0, hpoly,
    realGinibreCoreDensity_weighted_upper_eventual k α hα hk (δ/2) hε]
    with n hn hp hg
  calc
    _ ≤ (n : ℝ)*(∫ x : ℝ in Ioi 0, x^(2*k n)*realGinibreCoreDensity n x) :=
      gaussianMarkedRealDensity_weighted_integral_le_full_core n (k n) hn
    _ ≤ (n : ℝ)*Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) :=
      mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg n)
    _ ≤ Real.exp ((n : ℝ)*(δ/2))*Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms gaussianMarkedRealDensity_weighted_integral_le_full_core
#print axioms gaussianMarkedRealDensity_weighted_upper_eventual
end SpectralRadiusUpperTail
