import SpectralRadiusUpperTail.GaussianErfcCorrection
import SpectralRadiusUpperTail.RealGinibreFirstDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The nonreal one-point expression after extracting the dimensionless
Gaussian erfc correction. The two arguments are the radius and the
nonnegative scaled imaginary coordinate. -/
noncomputable def realGinibreNonrealDensity (n : ℕ) (s t : ℝ) : ℝ :=
  (n : ℝ)/Real.pi * gaussianErfcCorrection t *
    (Real.exp (-(n : ℝ)*s^2) *
      ginibreExpPartial (n-1) ((n : ℝ)*s^2))

/-- The erfc term never worsens the exterior Poisson rate. -/
theorem realGinibreNonrealDensity_bound (n : ℕ) (s t : ℝ)
    (hs : 1 ≤ s) (ht : 0 ≤ t) :
    0 ≤ realGinibreNonrealDensity n s t ∧
    realGinibreNonrealDensity n s t ≤
      (n : ℝ)/Real.pi * Real.exp (-(n : ℝ)*rate 2 s) := by
  have hc := gaussianErfcCorrection_bounds t ht
  have hx : 0 ≤ (n : ℝ)*s^2 := by positivity
  have hp : 0 ≤ ginibreExpPartial (n-1) ((n : ℝ)*s^2) := by
    unfold ginibreExpPartial
    exact Finset.sum_nonneg (fun k _ => div_nonneg (pow_nonneg hx _) (by positivity))
  have hm := ginibreExpPartial_mono (n-1) n (by omega)
    ((n : ℝ)*s^2) hx
  have hpoisson := ginibre_poisson_radius_bound n s hs
  have hfactor : 0 ≤ (n : ℝ)/Real.pi := by positivity
  constructor
  · unfold realGinibreNonrealDensity
    exact mul_nonneg (mul_nonneg hfactor hc.1)
      (mul_nonneg (Real.exp_pos _).le hp)
  · unfold realGinibreNonrealDensity
    calc
      _ ≤ (n : ℝ)/Real.pi *
            (Real.exp (-(n : ℝ)*s^2) *
              ginibreExpPartial (n-1) ((n : ℝ)*s^2)) := by
        have hq : 0 ≤ Real.exp (-(n : ℝ)*s^2) *
            ginibreExpPartial (n-1) ((n : ℝ)*s^2) :=
          mul_nonneg (Real.exp_pos _).le hp
        nlinarith [mul_le_mul_of_nonneg_right hc.2 hq]
      _ ≤ (n : ℝ)/Real.pi *
            (Real.exp (-(n : ℝ)*s^2) *
              ginibreExpPartial n ((n : ℝ)*s^2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le) hfactor
      _ ≤ _ := mul_le_mul_of_nonneg_left hpoisson hfactor

#print axioms realGinibreNonrealDensity_bound
end SpectralRadiusUpperTail
