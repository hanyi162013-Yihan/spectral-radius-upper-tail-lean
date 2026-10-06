import SpectralRadiusUpperTail.SchurGapGaussianTailIntegral
import SpectralRadiusUpperTail.GaussianErfcCorrection
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- Integrating the local real-Schur squared-gap density produces exactly
the dimensionless correction factor in the nonreal real-Ginibre one-point
expression. This is a scalar identity; it does not identify that expression
with a Gaussian matrix's actual eigenvalue intensity. -/
theorem schur_gap_integral_eq_erfc_correction (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    n*y * (∫ s : ℝ in Ioi 0,
      Real.exp (-(n/2)*s) *
        (Real.sqrt (s+4*y^2))⁻¹) =
      gaussianErfcCorrection (Real.sqrt (2*n)*y) := by
  rw [schur_gap_integral_eq_scaled_erfc n y hn hy]
  unfold gaussianErfcCorrection
  have hroot : 0 ≤ 2*n := by positivity
  have hsq : (Real.sqrt (2*n))^2 = 2*n := Real.sq_sqrt hroot
  have hpi : 0 ≤ Real.pi := Real.pi_nonneg
  have hdiv : 0 ≤ 2*Real.pi/n := by positivity
  have hpref : n*Real.sqrt (2*Real.pi/n) =
      Real.sqrt Real.pi * Real.sqrt (2*n) := by
    have hsqr := Real.sq_sqrt hdiv
    have hsqp := Real.sq_sqrt hpi
    have hnonneg1 : 0 ≤ n*Real.sqrt (2*Real.pi/n) := by positivity
    have hnonneg2 : 0 ≤ Real.sqrt Real.pi * Real.sqrt (2*n) := by positivity
    have hsqprefs : (n*Real.sqrt (2*Real.pi/n))^2 =
        (Real.sqrt Real.pi * Real.sqrt (2*n))^2 := by
      rw [mul_pow, hsqr, mul_pow, hsqp, hsq]
      field_simp [hn.ne']
    nlinarith
  have hexp : (Real.sqrt (2*n)*y)^2 = 2*n*y^2 := by
    rw [mul_pow, hsq]
  calc
    n*y * (Real.sqrt (2*Real.pi/n) * Real.exp (2*n*y^2) *
        gaussianErfc (Real.sqrt (2*n)*y)) =
      (n*Real.sqrt (2*Real.pi/n))*y*Real.exp (2*n*y^2)*
        gaussianErfc (Real.sqrt (2*n)*y) := by ring
    _ = (Real.sqrt Real.pi*Real.sqrt (2*n))*y*Real.exp (2*n*y^2)*
        gaussianErfc (Real.sqrt (2*n)*y) := by rw [hpref]
    _ = _ := by rw [hexp]; ring

/-- The local squared-gap integral obeys the sharp Mills-ratio bound after
the exact erfc identification. -/
theorem schur_gap_integral_mills_bound (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    0 ≤ n*y * (∫ s : ℝ in Ioi 0,
      Real.exp (-(n/2)*s) *
        (Real.sqrt (s+4*y^2))⁻¹) ∧
    n*y * (∫ s : ℝ in Ioi 0,
      Real.exp (-(n/2)*s) *
        (Real.sqrt (s+4*y^2))⁻¹) ≤ 1 := by
  rw [schur_gap_integral_eq_erfc_correction n y hn hy]
  exact gaussianErfcCorrection_bounds _ (by positivity)

#print axioms schur_gap_integral_eq_erfc_correction
#print axioms schur_gap_integral_mills_bound
end SpectralRadiusUpperTail
