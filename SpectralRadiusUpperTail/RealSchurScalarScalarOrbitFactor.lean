import SpectralRadiusUpperTail.RealSchurSpectralGapFactors
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The scalar–scalar mixed-block factor is the coefficient of the
off-diagonal infinitesimal orthogonal-conjugation direction. -/
theorem realSchur_scalar_scalar_orbit_factor (a u t : ℝ) :
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![a,0;0,u]
    let K : Matrix (Fin 2) (Fin 2) ℝ := !![0,-t;t,0]
    (K*D-D*K) 0 1 = (a-u)*t := by
  dsimp
  simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two]
  ring

theorem realSchur_scalar_scalar_orbit_abs_factor (a u : ℝ) :
    |(a-u)| = realSchurSpectralGap (.real a) (.real u) := rfl

#print axioms realSchur_scalar_scalar_orbit_factor
#print axioms realSchur_scalar_scalar_orbit_abs_factor
end SpectralRadiusUpperTail
