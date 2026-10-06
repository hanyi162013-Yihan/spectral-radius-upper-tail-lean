import SpectralRadiusUpperTail.MarkedRealStereoConeArea
import SpectralRadiusUpperTail.MarkedRealProductGaussianIntegral
import SpectralRadiusUpperTail.MarkedRealStereoAngularTransport
import SpectralRadiusUpperTail.GaussianRadialAngularNormalization

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The explicit hemisphere chart has exactly half the surface area of
the unit sphere. This is a change-of-variables computation, independent
of any assumed eigenvalue-density formula. -/
theorem markedRealStereoAngularWeight_lintegral (m : ℕ) :
    (∫⁻ w, markedRealStereoAngularWeight m w) =
      ENNReal.ofReal ((Real.sqrt Real.pi)^(m+1) /
        Real.Gamma (((m : ℝ)+1)/2)) := by
  let A := ∫⁻ u : Fin m → ℝ in {u | u ⬝ᵥ u < 1},
    ENNReal.ofReal ((2/markedRealStereoDenom m u)^m)
  let J := ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r^m) *
    ENNReal.ofReal (Real.exp (-r^2))
  have hJ := gaussian_radial_setLIntegral_bounds m
  have hcone : ENNReal.ofReal ((Real.sqrt Real.pi)^(m+1)/2) = J*A :=
    (markedRealProductGaussian_halfspace m).symm.trans
      (markedRealStereoCone_gaussian_area m)
  have hfull := gaussian_radial_sphere_product m
  rw [markedRealStereoAngularWeight_lintegral_reindex]
  change A = _
  apply (ENNReal.mul_left_inj hJ.1 hJ.2).mp
  apply (ENNReal.mul_right_inj (a := ENNReal.ofReal 2) (by norm_num) (by simp)).mp
  calc
    ENNReal.ofReal 2 * (A*J) = ENNReal.ofReal ((Real.sqrt Real.pi)^(m+1)) := by
      rw [mul_comm A J, ← hcone, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ = ENNReal.ofReal (2 * (Real.sqrt Real.pi)^(m+1) /
        Real.Gamma (((m : ℝ)+1)/2)) * J := hfull
    _ = _ := by
      rw [show 2 * (Real.sqrt Real.pi)^(m+1) / Real.Gamma (((m : ℝ)+1)/2) =
        2 * ((Real.sqrt Real.pi)^(m+1) / Real.Gamma (((m : ℝ)+1)/2)) by ring,
        ENNReal.ofReal_mul (by norm_num), mul_assoc]

#print axioms markedRealStereoAngularWeight_lintegral
end SpectralRadiusUpperTail
