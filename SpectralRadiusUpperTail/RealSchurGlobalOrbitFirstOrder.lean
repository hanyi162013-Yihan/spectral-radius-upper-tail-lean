import SpectralRadiusUpperTail.RealSchurGlobalBlockOrbitDiagonal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Matrix conjugation by `I+tK` has the commutator `KT-TK` as its exact
linear term, with a quadratic remainder. This gives the global orbit
coefficient used in the block-Jacobian calculations an actual matrix path. -/
theorem realSchur_global_orbit_first_order
    {n : ℕ} (T K : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + t • K) * T *
      ((1 : Matrix (Fin n) (Fin n) ℝ) - t • K) =
      T + t • (K*T-T*K) - t^2 • (K*T*K) := by
  simp only [add_mul, one_mul, mul_sub, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_assoc, smul_sub]
  module

#print axioms realSchur_global_orbit_first_order
end SpectralRadiusUpperTail
