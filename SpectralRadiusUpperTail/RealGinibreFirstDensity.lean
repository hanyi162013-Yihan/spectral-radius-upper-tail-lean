import SpectralRadiusUpperTail.GinibrePoissonRate
import SpectralRadiusUpperTail.RealGinibreDominantDensity

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The finite-Poisson part of the real one-point intensity. -/
noncomputable def realGinibreFirstDensity (n : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt ((n : ℝ)/(2*Real.pi)) *
    (Real.exp (-(n : ℝ)*r^2) *
      ginibreExpPartial (n-1) ((n : ℝ)*r^2))

lemma ginibreExpPartial_mono (m n : ℕ) (hmn : m ≤ n)
    (x : ℝ) (hx : 0 ≤ x) :
    ginibreExpPartial m x ≤ ginibreExpPartial n x := by
  unfold ginibreExpPartial
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun k _ _ => div_nonneg (pow_nonneg hx _) (by positivity))

theorem realGinibreFirstDensity_bound (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) :
    0 ≤ realGinibreFirstDensity n r ∧
    realGinibreFirstDensity n r ≤
      Real.sqrt ((n : ℝ)/(2*Real.pi)) *
        Real.exp (-(n : ℝ)*rate 2 r) := by
  have hx : 0 ≤ (n : ℝ)*r^2 := by positivity
  have hpart : 0 ≤ ginibreExpPartial (n-1) ((n : ℝ)*r^2) := by
    unfold ginibreExpPartial
    exact Finset.sum_nonneg (fun k _ => div_nonneg (pow_nonneg hx _) (by positivity))
  have hmono := ginibreExpPartial_mono (n-1) n (by omega)
    ((n : ℝ)*r^2) hx
  have hpoisson := ginibre_poisson_radius_bound n r hr
  constructor
  · unfold realGinibreFirstDensity
    positivity
  · unfold realGinibreFirstDensity
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le).trans hpoisson

#print axioms realGinibreFirstDensity_bound
end SpectralRadiusUpperTail
