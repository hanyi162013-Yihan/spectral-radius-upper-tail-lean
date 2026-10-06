import SpectralRadiusUpperTail.RealSchurPairInverseDensity
import SpectralRadiusUpperTail.RealSchurPairOrbitJacobian
import SpectralRadiusUpperTail.SchurGapWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The angular orbit Jacobian cancels the square-root gap singularity in
the inverse `(b,c) ↦ (u,s)` change of variables. What remains is precisely
the weight used in the product-model squared-gap law. This is a local
two-by-two calculation; the global real Schur law remains separate. -/
theorem realSchur_pair_gap_weight_from_jacobians
    (b c y : ℝ) (hc : 0 < c) (hcb : c < b)
    (hbc : b*c = y^2) :
    |Matrix.det (realSchurPairOrbitJacobian b c)| *
      realSchurPairInverseJacobian
        (realSchurPairCoordinates b c).1
        (realSchurPairCoordinates b c).2 =
      schurGapWeight y ((b-c)^2) := by
  have hdiff : 0 < b-c := sub_pos.mpr hcb
  have hsum : 0 < b+c := by linarith
  have hsqrtDiff : Real.sqrt ((b-c)^2) = b-c := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hdiff]
  have hsq : (b-c)^2+4*y^2 = (b+c)^2 := by
    nlinarith [hbc]
  have hsqrtSum : Real.sqrt ((b-c)^2+4*y^2) = b+c := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hsum]
  have hs0 : 0 ≤ (b-c)^2 := sq_nonneg _
  rw [realSchur_pair_orbit_jacobian_abs b c hcb]
  unfold realSchurPairInverseJacobian schurGapWeight
    realSchurPairCoordinates
  rw [hbc, hsqrtDiff, hsqrtSum]
  simp only [max_eq_right hs0, hsqrtSum]
  field_simp

/-- Gaussian block energy and the two local Jacobians combine into the
spectral Gaussian factor times the squared-gap density factor. -/
theorem realSchur_pair_local_gaussian_factor
    (n x b c y : ℝ) (hc : 0 < c) (hcb : c < b)
    (hbc : b*c = y^2) :
    |Matrix.det (realSchurPairOrbitJacobian b c)| *
      realSchurPairInverseJacobian
        (realSchurPairCoordinates b c).1
        (realSchurPairCoordinates b c).2 *
      Real.exp (-(n/2)*(2*x^2+b^2+c^2)) =
        schurGapWeight y ((b-c)^2) *
          (Real.exp (-n*(x^2+y^2)) *
            Real.exp (-(n/2)*(b-c)^2)) := by
  rw [← realSchur_pair_gap_weight_from_jacobians b c y hc hcb hbc]
  rw [← realSchur_pair_gaussian_weight n x b c y hbc]

#print axioms realSchur_pair_gap_weight_from_jacobians
#print axioms realSchur_pair_local_gaussian_factor
end SpectralRadiusUpperTail
